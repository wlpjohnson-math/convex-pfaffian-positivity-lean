import PfaffianLean

open Finset in
#eval pfaffian (Icc 1 4) (Matrix.of fun i j => ((10 * i + j : ℕ) : ℤ))  -- expect 418

#check @pfaffian_insert_of_forall_lt   -- shows the full statement
#print pfaffian                         -- shows the definition
