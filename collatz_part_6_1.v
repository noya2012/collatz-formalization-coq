(* Independent Theorem Extraction *)
Load "collatz_part_6.v".
Lemma build_k_steps_length_min : forall n k,
  valid_input n ->
  length (build_k_steps n k) >= k.
Proof.
induction k; intros Hvalid.
- simpl. lia.
- simpl build_k_steps.
remember (sequence_end n (build_k_steps n k)) as curr_n.
destruct (Nat.even curr_n).
+ rewrite app_length. simpl.
specialize (IHk Hvalid).
lia.
+ rewrite app_length. simpl.
specialize (IHk Hvalid).
lia.
Qed.

(* Main theorem: Proof that in a k-step sequence, the number of R0 operations is exactly k, 
   then the number of R1 operations does not exceed k, and the total length does not exceed 2k.
   This shows that R0 operations (n/2) dominate in the sequence, supporting the intuition 
   that the sequence will eventually converge. *)
Theorem build_k_steps_structure : forall n k,
  valid_input n ->
  k >= 2 ->
  exists ops r0s r1s,
  build_k_steps n k = ops /\
  count_operations ops = (r0s, r1s) /\
  r0s = k /\           (* Strengthened: R0 count is exactly k *)
  r1s <= k /\          (* R1 count is at most k *)
  r1s = length ops - k (* New: Exact value of R1 *) /\
  length ops <= 2 * k. (* Total length is at most 2k *)
Proof.
intros n k Hvalid Hk.
assert (HR0: let (r0s, _) := count_operations (build_k_steps n k) in r0s = k).
{ apply (R0_count_eq_k n k (build_k_steps n k)).
- exact Hvalid.
- lia.
- reflexivity. }
assert (Hlen: length (build_k_steps n k) <= 2 * k).
{ apply build_k_steps_length_bound. assumption. }
assert (Hsum: let (r0s, r1s) := count_operations (build_k_steps n k) in
r0s + r1s = length (build_k_steps n k)).
{ apply count_sum_c2. }
destruct (count_operations (build_k_steps n k)) as [r0s r1s] eqn:Hcount.
exists (build_k_steps n k), r0s, r1s.
split; [reflexivity|].
split; [assumption|].
split.
-
rewrite HR0. reflexivity.
- split.
+
assert (r0s + r1s <= 2 * k).
{ rewrite Hsum. assumption. }
rewrite HR0 in H.
lia.
+ split.
*
rewrite <- Hsum.
rewrite HR0.
lia.
*
assumption.
Qed.

Theorem build_k_steps_increment_basic : forall n k,
  valid_input n ->
  k >= 2 ->
  let (r0s_k, r1s_k) := count_operations (build_k_steps n k) in
  let (r0s_next, r1s_next) := count_operations (build_k_steps n (S k)) in
  r0s_next = r0s_k + 1 /\                    (* R0 increases exactly by 1 *)
  r1s_next <= r1s_k + 1.                     (* R1 increases at most by 1 *)
Proof.
intros n k Hvalid Hk.
destruct (build_k_steps_structure n k Hvalid Hk)
as [ops_k [r0s_k' [r1s_k' [Heq_k [Hcount_k [Hr0s_k [Hr1s_k _]]]]]]].
pose proof (build_k_steps_Sn n k Hvalid) as H_build.
rewrite Heq_k in H_build.
destruct (count_operations (build_k_steps n k)) as [r0s_k r1s_k] eqn:Hcount1.
destruct (count_operations (build_k_steps n (S k))) as [r0s_next r1s_next] eqn:Hcount2.
destruct (Nat.even (sequence_end n ops_k)) eqn:E.
-
split.
+
assert (H_chain: exists r0s_new r1s_new,
count_operations (ops_k ++ [R0]) = (r0s_new, r1s_new) /\
r0s_new = r0s_k + 1).
{
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
exists (r0s_old + 1), r1s_old.
pose proof (count_operations_app_R0 ops_k) as H_count.
rewrite Hold in H_count.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
split.
-
destruct (count_operations (ops_k ++ [R0])) eqn:Hnew.
destruct H_count as [H_r0' H_r1'].
f_equal; auto.
-
rewrite Hr0s_eq.
reflexivity.
}
destruct H_chain as [r0s_new [r1s_new [H_new H_eq]]].
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
rewrite H_new in Hcount2.
injection Hcount2 as H_next _.
rewrite <- H_next.
exact H_eq.
+
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
pose proof (count_operations_app_R0 ops_k) as H_count.
rewrite Hold in H_count.
destruct (count_operations (ops_k ++ [R0])) eqn:Hnew.
destruct H_count as [_ H_r1].
injection Hcount2 as _ H_r1_next.
rewrite <- H_r1_next.
rewrite <- Hr1s_eq.
rewrite H_r1.
lia.
-
split.
+
assert (H_chain: exists r0s_new r1s_new,
count_operations (ops_k ++ [R1; R0]) = (r0s_new, r1s_new) /\
r0s_new = r0s_k + 1).
{
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
exists (S r0s_old), (S r1s_old).
pose proof (count_operations_app_R1R0 ops_k) as H_count.
rewrite Hold in H_count.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
split.
-
destruct (count_operations (ops_k ++ [R1; R0])) eqn:Hnew.
destruct H_count as [H_r0' H_r1'].
f_equal.
+
exact H_r0'.
+
exact H_r1'.
-
rewrite Hr0s_eq.
lia.
}
destruct H_chain as [r0s_new [r1s_new [H_new H_eq]]].
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
rewrite H_new in Hcount2.
injection Hcount2 as H_next _.
rewrite <- H_next.
exact H_eq.
+
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
pose proof (count_operations_app_R1R0 ops_k) as H_count.
rewrite Hold in H_count.
destruct (count_operations (ops_k ++ [R1; R0])) eqn:Hnew.
destruct H_count as [_ H_r1].
injection Hcount2 as _ H_r1_next.
rewrite <- H_r1_next.
rewrite <- Hr1s_eq.
rewrite H_r1.
lia.
Qed.
