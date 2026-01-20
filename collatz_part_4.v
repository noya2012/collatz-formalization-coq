
Load "collatz_part_3.v".

(* 2. Validity of single-step operation *)
Lemma single_step_valid : forall n op,
  valid_input n ->
  valid_operation n op ->
  valid_input (collatz_step n).
Proof.
intros n op Hvalid Hop.
unfold valid_input in *.
unfold collatz_step.
destruct op.
-
unfold valid_operation in Hop.
rewrite Hop.
assert (n >= 2).
{
destruct n; try lia.
destruct n; try lia.
unfold is_even in Hop.
simpl in Hop.
discriminate.
}
apply Nat.div_le_lower_bound; lia.
-
unfold valid_operation in Hop.
rewrite Hop.
lia.
Qed.

(* Inductive property of sequence validity *)
Lemma valid_sequence_inductive : forall n ops,
  valid_input n ->
  (forall i, i < length ops -> valid_operation (nth_sequence_value n i) (nth i ops R0)) ->
  forall k, k <= length ops ->
  valid_input (nth_sequence_value n k).
Proof.
intros n ops Hvalid Hseq k Hk.
induction k.
-
simpl. assumption.
-
simpl.
apply single_step_valid with (op := nth k ops R0).
+
apply IHk. lia.
+
apply Hseq. lia.
Qed.


(* Recursive property of sequence values *)
Lemma nth_sequence_value_succ : forall n i,
  nth_sequence_value n (S i) = collatz_step (nth_sequence_value n i).
Proof.
intros n i.
reflexivity.
Qed.

