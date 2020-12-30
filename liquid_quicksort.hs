import qualified Data.Set as DS

{-@ measure elts @-}
elts        :: (Ord a) => [a] -> DS.Set a
elts []     = DS.empty
elts (x:xs) = DS.singleton x `DS.union` elts xs

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs

{-@ type ListS a S = {v:[a] | elts v == S} @-}
{-@ type ListUn a X Y = ListS a (DS.Set_cup (elts X) (elts Y)) @-}

{-@ type SortedList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type SortedListS a S = { v:SortedList a | elts v == S } @-}
{-@ type SortedListUn a X Y = SortedListS a {Set_cup (elts X) (elts Y)} @-}

-- Mimicking definition from Coq standard library does not work, as we get a redundant case error
-- for the last line in this definition
-- {-@ measure perm @-}
-- {-@ perm :: [a] -> [a] -> Bool @-}
-- perm [] [] = True
-- perm [] _ = False
-- perm _ [] = False
-- perm (x:xs) (y:ys) = (x == y) && (perm xs ys)
-- perm (x:x':xs) (y:y':ys) = (x == y) && (x' == y') && perm xs ys

{-@ sappend :: x:a -> l1:SortedList { v:a | x >= v } -> l2:SortedList { v':a | x < v' } -> 
        { lo:SortedListS a (Set_cup (DS.singleton x) (Set_cup (elts l1) (elts l2))) | size lo == size l1 + size l2 + 1 } @-}
sappend x [] xs = x : xs
sappend x (y : ys) xs = y : (sappend x ys xs)

-- Termination not checked correctly when using list comprehensions as in earlier example
-- We add a lot of information to the refinement type for split to ensure the quicksort function
-- is found to be safe
{-@ split :: n:a -> l:[a] ->
        { pl:([{x:a | x <= n}],[{y:a | y > n}]) | elts l == Set_cup (elts (fst pl)) (elts (snd pl)) &&
                                                  size (fst pl) <= size l && size (snd pl) <= size l &&
                                                  size l == size (fst pl) + size (snd pl) } @-}
split :: Ord a => a -> [a] -> ([a],[a])
split _ [] = ([],[])
split n (x:xs)
    | x <= n = (x:f,s)
    | otherwise = (f,x:s)
    where (f,s) = split n xs

-- Interesting: UNSAFE when leaving out [size v] termination annotation
-- Seems this would be the obvious choice
-- Error message also does not mention termination, just failed type checking
{-@ quicksort :: Ord a => v:[a] -> { v':SortedListS a (elts v) | size v' == size v } / [size v] @-}
quicksort [] = []
quicksort (x : xs) = sappend x (quicksort small) (quicksort large)
    where (small, large) = split x xs

