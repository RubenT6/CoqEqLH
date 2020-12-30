-- BST exercise from LiquidHaskell book
-- We take all definitions apart from IncList, sappend and toIncList from the book

{-@ type Nat = Int<{\x -> x >= 0}> @-}

{-@ data Tree a <l :: a -> a -> Bool, r :: a -> a -> Bool> = 
          Leaf
        | Node { root :: a
            , left :: Tree <l, r> (a <l root>)
            , right :: Tree <l, r> (a <r root>) } @-}

data Tree a = Leaf
            | Node { root :: a
                    , left :: Tree a
                    , right :: Tree a }

{-@ type BST a = Tree<{\x y -> y <= x}, {\x y -> x < y}> a @-}
type BST a = Tree a

--{-@ data BST a = Leaf
--                | Node { root :: a
--                , left :: BST {x:a | x < root}
--                , right :: BST {x:a | root < x} } @-}

{-@ type BSTL a X = BST {v:a | v < X} @-}
{-@ type BSTR a X = BST {v:a | X < v} @-}

{-@ one :: a -> BST a @-}
one :: a -> BST a
one x = Node x Leaf Leaf

{-@ add :: (Ord a) => a -> BST a -> BST a @-}
add :: (Ord a) => a -> BST a -> BST a
add k' Leaf = one k'
add k' t@(Node k l r)
    | k' <= k = Node k (add k' l) r
    | k < k' = Node k l (add k' r)
    | otherwise = t

{-@ type IncList a = [a]<{\x1 x2 -> x1 <= x2}> @-}

{-@ bstSort :: (Ord a) => [a] -> IncList a @-}
bstSort :: (Ord a) => [a] -> [a]
bstSort = toIncList . toBST

{-@ toBST :: (Ord a) => [a] -> BST a @-}
toBST :: (Ord a) => [a] -> BST a
toBST = foldr add Leaf

{-@ sappend :: x:a -> IncList { v:a | v <= x } -> IncList { v':a | x < v' } -> IncList a @-}
sappend x [] xs = x : xs
sappend x (y : ys) xs = y : (sappend x ys xs)

{-@ toIncList :: BST a -> IncList a @-}
toIncList :: BST a -> [a]
toIncList (Node x l r) = sappend x (toIncList l) (toIncList r)
toIncList Leaf = []
