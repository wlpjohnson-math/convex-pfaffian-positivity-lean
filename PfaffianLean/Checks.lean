import PfaffianLean

open Finset
#eval pfaffian (Icc 1 4) (Matrix.of fun i j => ((10 * i + j : ℕ) : ℤ))  -- expect 418

#check @pfaffian_insert_of_forall_lt   -- shows the full statement
#print pfaffian                         -- shows the definition

/-- Satisfiability check: the hypotheses of `convex_lower_bound` hold for `f = 1`, `x k = k`. -/
example (n : ℕ) (hn : Even n) :
    pfaffian (Icc 1 n) (kernel (fun _ => (1 : ℝ)) (fun k => (k : ℝ))) ≥ (1 : ℝ) ^ (n / 2) ∧
      (1 : ℝ) ^ (n / 2) > 0 := by
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < (fun _ : ℝ => (1 : ℝ)) t := fun _ _ => one_pos
  have hanti : AntitoneOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := fun _ _ _ _ _ => le_rfl
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun _ : ℝ => (1 : ℝ)) := convexOn_const 1 (convex_Ioi 0)
  have hx : StrictMonoOn (fun k : ℕ => (k : ℝ)) (Set.Icc 1 n) := fun a _ b _ hab =>
    show (a : ℝ) < b from Nat.cast_lt.2 hab
  exact convex_lower_bound (fun _ => 1) hpos hanti hconv n hn (fun k => (k : ℝ)) hx

#check @convex_lower_bound

#print axioms convex_lower_bound
