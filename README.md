# CoqEqLH
A comparison of Coq-Equations and LiquidHaskell
## Description of files
### `equations_quicksort.v`
Gallina file containing definition of quicksort algorithm using the Equations extension for Coq.
Also contains proofs of correctness: sorting and permutation properties.
### `equations_mergesort.v`
Same as `equations_quicksort.v` but now for the mergesort algorithm.
Unfortunately, does not include proof of permutation property at this time (due to use of `vector` type)
### `equations_BSTSort.v`
Contains definition of Tree and BST invariant as well as sorting algorithm based on these structures.
Also include proof of sorting property.
### `equations_app_sigma_vs_nosigma.v`
Interesting example of issues encountered due to use of dependent type `vector`.
### `liquid_quicksort.hs`, `liquid_mergesort.hs` and `liquidBST.hs`
Similar to their `equations counterparts above. Currently none contain proofs of permutation property.
### `liquid_natpos.hs`
Very simple example used to explain part of the verification method employed by LH.
