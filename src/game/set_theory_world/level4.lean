/- Tactic : rwa


`rwa` uses the rewrite tactic and then uses `exact` with all 
the assumptions of the proof.

-/


/- 
The next tactic we will learn is `rwa` which applies rewrite tactic and then uses `exact` with all the hypotheses.
-/


variables {X : Type} -- hide

/- Lemma : no-side-bar
Let A be a set and x ∈ A, using the assumption A ∪ A = A, we obtain that x ∈ B.
-/
lemma example_on_rwa (A : set X) (x : X) (h1 : x ∈ A) (h2 : A ∪ A = A) : x ∈ A ∪ A :=
begin
  rwa h2,
  


end