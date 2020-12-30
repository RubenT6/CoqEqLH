{-@ type Nat = { n:Int | n >= 0 } @-}
{-@ type Pos = { n:Int | n > 0 } @-}

{-@ mys :: Nat -> Pos @-}
mys :: Int -> Int
mys n = n + 1
