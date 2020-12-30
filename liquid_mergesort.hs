import qualified Data.Set as DS

{-@ measure elts @-}
elts        :: (Ord a) => [a] -> DS.Set a
elts []     = DS.empty
elts (x:xs) = DS.singleton x `DS.union` elts xs

{-@ type ListS a S = {v:[a] | elts v = S} @-}
{-@ type ListUn a X Y = ListS a {DS.Set_cup (elts X) (elts Y)} @-}

{-@ type SortedList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type SortedListS a S = { v:SortedList a | elts v = S } @-}
{-@ type SortedListUn a X Y = SortedListS a {Set_cup (elts X) (elts Y)} @-}

-- It seems that LiquidHaskell struggles to recognize the decreasing arguments for merge
-- We can use the [bound] notation to manually specify this

{-@ type Nat = { v:Int | 0 <= v } @-}

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs

{-@ merge :: Ord a => xs:SortedList a -> ys:SortedList a ->
        { zs:SortedListUn a xs ys | size zs == size xs + size ys } / [size xs + size ys] @-}
merge :: (Ord a) => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
    | (x <= y) = x:merge xs (y:ys)
    | otherwise = y:merge (x:xs) ys

-- @ take' :: l:[a] -> m:{ n:Int | n <= size l } -> { v:[a] | size v = m } @
-- take' :: [a] -> Int -> [a]
-- take' _ 0 = []
-- take' (x:t) n = x:(take' t (n-1))

-- @ splitinhalf :: v:{ v1:[a] | size v >= 2 } -> ({ v2:[a] | size v2 < size v }, { v3:[a] | size v3 < size v }) @
-- splitinhalf :: [a] -> ([a], [a])
-- splitinhalf xs = (take' xs n, drop n xs)
--     where n = (length xs) `div` 2 

{-@ halve' :: v1:[a] ->
        { pv:({ v2:[a] | size v2 = size v1 / 2 }, { v3:[a] | size v3 = size v1 - size v1 / 2 }) | elts v1 == Set_cup (elts (fst pv)) (elts (snd pv)) &&
                                                                                                  size v1 == size (fst pv) + size (snd pv) } @-}
halve' [] = ([],[])
halve' [x] = ([],[x])
halve' (h:k:t) = (h:t1, k:t2) where (t1,t2) = halve' t

-- (strange?) definition taken from liquidhaskell docs
-- doesn't work at the moment, above definition is better
-- {-@ halve :: n:Int -> l:[a] -> { p:([a],[a]) | n > 0 => size l >= 2 => (size (fst p) < size l && size (snd p) < size l) } @-}
-- halve            :: Int -> [a] -> ([a], [a])
-- halve 0 xs       = ([], xs)
-- halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
-- halve _ xs       = ([], xs)

{-@ mergesort :: Ord a => v:[a] -> { v':SortedListS a (elts v) | size v' == size v } / [size v] @-}
mergesort :: (Ord a) => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort (xs) = merge (mergesort ls) (mergesort rs)
    where (ls, rs) = halve' xs

-- mergesort xs 
--     | (length xs) > 1 = mergesort'merge (mergesort ls) (mergesort rs)
--     | otherwise = xs
--     where (ls, rs) = mergesort'splitinhalf xs
    