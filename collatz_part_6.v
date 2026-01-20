Load "collatz_part_5.v".




(* Properties of sequence construction *)
Lemma build_k_steps_valid : forall n k,
  valid_input n ->
  valid_sequence (build_k_steps n k) n.
Proof.
intros n k Hvalid.
induction k as [|k' IHk].
-
simpl. unfold valid_sequence. intros. simpl in H. lia.
-
simpl build_k_steps.
remember (sequence_end n (build_k_steps n k')) as curr_n.
assert (Hvalid_curr : valid_input curr_n).
{ rewrite Heqcurr_n.
apply sequence_end_valid with (ops := build_k_steps n k').
- exact Hvalid.
- exact IHk. }
destruct (Nat.even curr_n) eqn:Heven.
+
assert (Hvalid_new: valid_sequence (build_k_steps n k' ++ [R0]) n).
{ unfold valid_sequence in *. intros i Hi.
rewrite app_length in Hi. simpl in Hi.
destruct (Nat.eq_dec i (length (build_k_steps n k'))) as [Heq|Hneq].
-
rewrite Heq.
unfold valid_operation.
assert (Hseq: curr_n = nth_sequence_value n (length (build_k_steps n k'))).
{ unfold sequence_end in Heqcurr_n.
exact Heqcurr_n. }
rewrite <- Hseq.
rewrite nth_append_last.
unfold is_even. exact Heven.
-
assert (i < length (build_k_steps n k')) by lia.
assert (nth i (build_k_steps n k' ++ [R0]) R0 = nth i (build_k_steps n k') R0).
{ rewrite app_nth1; auto. }
rewrite H0.
apply IHk.
exact H. }
exact Hvalid_new.
+
assert (Hvalid_new: valid_sequence (build_k_steps n k' ++ [R1; R0]) n).
{ unfold valid_sequence in *. intros i Hi.
rewrite app_length in Hi. simpl in Hi.
destruct (Nat.eq_dec i (length (build_k_steps n k'))) as [Heq1|Hneq1].
-
rewrite Heq1.
unfold valid_operation.
assert (Hseq: curr_n = nth_sequence_value n (length (build_k_steps n k'))).
{ unfold sequence_end in Heqcurr_n.
exact Heqcurr_n. }
rewrite <- Hseq.
pose proof (nth_append_two (build_k_steps n k') R1 R0) as [H1 H2].
rewrite H1.
unfold is_odd.
exact Heven.
- destruct (Nat.eq_dec i (S (length (build_k_steps n k')))) as [Heq2|Hneq2].
+
rewrite Heq2.
unfold valid_operation.
assert (Hodd: is_odd curr_n).
{ unfold is_odd. exact Heven. }
pose proof (nth_append_two (build_k_steps n k') R1 R0) as [H1 H2].
rewrite H2.
assert (Hstep: nth_sequence_value n (S (length (build_k_steps n k'))) = 3 * curr_n + 1).
{
rewrite nth_sequence_value_succ.
unfold collatz_step.
assert (Hseq: nth_sequence_value n (length (build_k_steps n k')) = curr_n).
{ symmetry. exact Heqcurr_n. }
rewrite Hseq.
rewrite Heven.
reflexivity.
}
rewrite Hstep.
unfold is_even.
apply even_3n_plus_1.
exact Hodd.
+
assert (i < length (build_k_steps n k')) by lia.
assert (nth i (build_k_steps n k' ++ [R1; R0]) R0 = nth i (build_k_steps n k') R0).
{ rewrite app_nth1; auto. }
rewrite H0.
apply IHk.
exact H. }
exact Hvalid_new.
Qed.


(* Auxiliary lemma about sequence construction *)
Lemma build_k_steps_Sn : forall n k,
  valid_input n ->
  build_k_steps n (S k) =
  let prev_ops := build_k_steps n k in
  let curr_n := sequence_end n prev_ops in
  if Nat.even curr_n
  then prev_ops ++ [R0]
  else prev_ops ++ [R1; R0].
Proof.
intros n k Hvalid.
simpl. reflexivity.
Qed.



(* Sequence length is at least k and at most 2k *)
Lemma build_k_steps_length_bound : forall n k,
  valid_input n ->
  k <= length (build_k_steps n k) <= 2 * k.
Proof.
induction k; intros Hvalid.
-
simpl. split; lia.
-
simpl build_k_steps.
remember (sequence_end n (build_k_steps n k)) as curr_n.
destruct (Nat.even curr_n).
+
rewrite app_length. simpl.
specialize (IHk Hvalid).
split.
*
lia.
*
lia.
+
rewrite app_length. simpl.
specialize (IHk Hvalid).
split.
*
lia.
*
lia.
Qed.

(* R0 count equals k *)
Lemma R0_count_eq_k : forall n k ops,
  valid_input n ->
  k >= 1 ->
  build_k_steps n k = ops ->
  let (r0s, _) := count_operations ops in
  r0s = k.
Proof.
intros n k ops Hvalid Hk Heq.
generalize dependent ops.
induction k as [|k' IHk].
-
intros ops Heq.
lia.
-
intros ops Heq.
simpl build_k_steps in Heq.
remember (sequence_end n (build_k_steps n k')) as curr_n.
assert (Hvalid_curr : valid_input curr_n).
{ rewrite Heqcurr_n.
apply sequence_end_valid with (ops := build_k_steps n k').
- exact Hvalid.
- apply build_k_steps_valid; auto. }
destruct (Nat.even curr_n) eqn:Heven.
+
rewrite <- Heq.
destruct k' as [|k''].
*
simpl.
destruct (count_operations (build_k_steps n 0)) as [r0s_old r1s_old].
destruct (count_operations (build_k_steps n 0 ++ [R0])) as [r0s_new r1s_new].
simpl in *.
reflexivity.
*
destruct (count_operations (build_k_steps n (S k''))) as [r0s_old r1s_old].
assert (H_prev: let (r0s, _) := count_operations (build_k_steps n (S k'')) in r0s = S k'').
{
apply IHk.
- lia.
- reflexivity.
}
destruct (count_operations (build_k_steps n (S k''))) as [r0s' r1s'] eqn:Heq_old.
destruct (count_operations (build_k_steps n (S k'') ++ [R0])) as [r0s_new r1s_new] eqn:Heq_new.
assert (r0s_new = S r0s').
{
pose proof (count_operations_app_R0 (build_k_steps n (S k''))) as H_count.
rewrite Heq_old in H_count.
rewrite Heq_new in H_count.
destruct H_count as [H_count _].
rewrite Nat.add_1_r in H_count.
exact H_count.
}
rewrite H.
rewrite H_prev.
reflexivity.
+
rewrite <- Heq.
destruct k' as [|k''].
*
simpl.
destruct (count_operations (build_k_steps n 0)) as [r0s_old r1s_old].
destruct (count_operations (build_k_steps n 0 ++ [R1; R0])) as [r0s_new r1s_new].
simpl in *.
reflexivity.
*
destruct (count_operations (build_k_steps n (S k''))) as [r0s_old r1s_old].
assert (H_prev: let (r0s, _) := count_operations (build_k_steps n (S k'')) in r0s = S k'').
{
apply IHk.
- lia.
- reflexivity.
}
destruct (count_operations (build_k_steps n (S k''))) as [r0s' r1s'] eqn:Heq_old.
destruct (count_operations (build_k_steps n (S k'') ++ [R1; R0])) as [r0s_new r1s_new] eqn:Heq_new.
assert (r0s_new = S r0s').
{
pose proof (count_operations_app_R1R0 (build_k_steps n (S k''))) as H_count.
rewrite Heq_old in H_count.
rewrite Heq_new in H_count.
destruct H_count as [H_count _].
exact H_count.
}
rewrite H.
rewrite H_prev.
reflexivity.
Qed.

