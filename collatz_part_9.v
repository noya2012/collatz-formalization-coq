Load "collatz_part_8.v".

(* When D = 1: On the corresponding entry, repeat_R1R0 generates [R1; R0], and the consecutive R1R0 count is 1 *)
Lemma valid_R1R0_d1_produces_R1R0 : forall n,
  n >= 0 ->
  let m := valid_R1R0_entry_number 1 n in
  valid_sequence [R1; R0] m /\ count_consecutive_R1R0 [R1; R0] = 1.
Proof.
intros n Hn m. unfold m.
pose proof (valid_R1R0_entry_number_properties 1 n (le_n 1) Hn) as [Hvalid_m Hodd_m].
split.
- unfold valid_sequence. intros i Hi. simpl in Hi.
destruct i as [|i'].
+
simpl. exact Hodd_m.
+
destruct i' as [|i''].
*
simpl.
unfold collatz_step.
rewrite Hodd_m.
simpl.
apply even_3n_plus_1; exact Hodd_m.
*
lia.
- simpl. reflexivity.
Qed.

(* The length of repeat_R1R0 is exactly 2 * d *)
Lemma repeat_R1R0_length : forall d,
  length (repeat_R1R0 d) = 2 * d.
Proof.
induction d as [|d' IH].
- simpl. reflexivity.
- simpl. rewrite IH. lia.
Qed.

(* The number of consecutive R1R0 patterns in repeat_R1R0 equals d *)
Lemma repeat_R1R0_count : forall d,
  count_consecutive_R1R0 (repeat_R1R0 d) = d.
Proof.
induction d as [|d' IH].
- simpl. reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.

(* For any D >= 1: when m = valid_R1R0_entry_number D n,
repeat_R1R0 D is valid on m and contains D consecutive R1R0 patterns *)

Lemma valid_R1R0_produces_R1R0_general : forall D n,
  D >= 1 ->
  n >= 0 ->
  let m := valid_R1R0_entry_number D n in
  valid_sequence (repeat_R1R0 D) m /\
  count_consecutive_R1R0 (repeat_R1R0 D) = D.
Proof.
intros D. induction D as [|D' IH]; intros n HD Hn m; unfold m.
- lia.
- destruct D' as [|d1].
+ apply valid_R1R0_d1_produces_R1R0; assumption.
+
set (Dfull := S (S d1)).
assert (Hd_full: Dfull >= 1) by lia.
pose proof (valid_R1R0_entry_number_properties Dfull n Hd_full Hn) as [_ Hodd_m].
pose proof (R1R0_pattern_closure Dfull n Hd_full Hn) as Hcl.
set (n' := 3 * n + 1).
assert (Hd_tail: S d1 >= 1) by lia.
specialize (IH n' Hd_tail (Nat.le_0_l n')).
destruct IH as [Hseq_tail Hcount_tail].
split.
* intros i Hi. simpl in Hi. destruct i as [|i']; [simpl; exact Hodd_m |].
destruct i' as [|i'']; [simpl; unfold collatz_step; rewrite Hodd_m; simpl; apply even_3n_plus_1; exact Hodd_m |].
simpl.
change (collatz_step (collatz_step (nth_sequence_value (valid_R1R0_entry_number Dfull n) i'')))
with (nth_sequence_value (valid_R1R0_entry_number Dfull n) (S (S i''))).
change (nth_sequence_value (valid_R1R0_entry_number Dfull n) (S (S i'')))
with (nth_sequence_value (valid_R1R0_entry_number Dfull n) (2 + i'')).
rewrite (nth_sequence_value_app (valid_R1R0_entry_number Dfull n) 2 i'').
change (nth_sequence_value (valid_R1R0_entry_number Dfull n) 2)
with (sequence_end (valid_R1R0_entry_number Dfull n) [R1; R0]).
rewrite Hcl. apply Hseq_tail.
rewrite repeat_R1R0_length in Hi |- *.
simpl in Hi. lia.
* simpl. rewrite repeat_R1R0_count. unfold Dfull. reflexivity.
Qed.

(* If m = valid_R1R0_entry_number d n, then repeat_R1R0 d is valid on m and the count is d *)
Lemma R1R0_entry_number_produces_repeat : forall d n,
  d >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number d n in
  valid_sequence (repeat_R1R0 d) m /\ count_consecutive_R1R0 (repeat_R1R0 d) = d.
Proof.
intros d n Hd Hn m. unfold m. apply valid_R1R0_produces_R1R0_general; assumption.
Qed.


(* Special case d = 0: valid_R1R0_entry_number 0 n = 2 * n *)
Lemma valid_R1R0_entry_number_d0 : forall n,
  valid_R1R0_entry_number 0 n = 2 * n.
Proof.
intros n.
unfold valid_R1R0_entry_number.
cbn [Nat.pow Nat.mul Nat.add Nat.sub].
lia.
Qed.

(* For D >= 1: The final value after applying repeat_R1R0 D on the corresponding entry is even (exists k such that it equals 2*k)
To reach a power of 2, this means 3^D * n + (3^D - 1)/2 = n₂ * 2^D₂, Catalan theorem *)
Lemma repeat_R1R0_output_even : forall D n,
  D >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number D n in
  exists k, sequence_end m (repeat_R1R0 D) = 2 * k.
Proof.
intro D.
induction D as [|D' IH]; intros n HD Hn.
- lia.
- destruct D' as [|d].
+
simpl.
rewrite (R1R0_pattern_closure 1 n (le_n 1) Hn).
rewrite valid_R1R0_entry_number_d0.
exists (3 * n + 1). reflexivity.
+
assert (Hrep: repeat_R1R0 (S (S d)) = [R1; R0] ++ repeat_R1R0 (S d)).
{ simpl. reflexivity. }
rewrite Hrep.
unfold sequence_end at 1.
rewrite app_length.
rewrite nth_sequence_value_app.
change (nth_sequence_value (valid_R1R0_entry_number (S (S d)) n) (length [R1; R0]))
with (sequence_end (valid_R1R0_entry_number (S (S d)) n) [R1; R0]).
rewrite (R1R0_pattern_closure (S (S d)) n); try lia.
assert (Hd_ge: S d >= 1) by lia.
apply IH with (n := 3 * n + 1); try lia.
Qed.


(* ============================================================= *)

(* Catalan theorem application: 3^a - 2^b = 1 only has solution (a,b) = (2,3)
Theorem repeat_R1R0_power_of_2_classification : forall D n,
  D >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number D n in
  let output := sequence_end m (repeat_R1R0 D) in
  (exists k, output = 2^k) <->
  match D with
  | 1 => exists k, 3 * n + 1 = 2^k
  | 2 => exists k, 9 * n + 4 = 2^k
  | _ => (* Complex conditions strictly limited by Catalan theorem *)
         exists k, 3^D * n + (3^D - 1)/2 = 2^k /\
         catalan_constraint D k
  end.*)

  
(* R1R0 arithmetic identity: recursive entry parameter equation *)
Lemma arithmetic_identity_for_R1R0 : forall k n,
  k >= 0 -> n >= 0 ->
  3^(S k) * n + (3^(S k) - 1) / 2 =
  3^k * (3*n+1) + (3^k - 1) / 2.
Proof.
intros k n _ Hn.
rewrite pow3_expand.
assert (A: (3 * 3 ^ k - 1) / 2 = 3 ^ k + (3 ^ k - 1) / 2).
{
assert (E: 3 * 3 ^ k - 1 = 3 ^ k * 2 + (3 ^ k - 1)) by lia.
rewrite E.
assert (H2: 2 <> 0) by lia.
rewrite (Nat.div_add_l (3 ^ k) 2 (3 ^ k - 1) H2).
reflexivity.
}
rewrite A. ring.
Qed.

(* In R1R0 mode, expression of final value under repeat_R1R0 prefix application *)
Lemma sequence_end_valid_R1R0_prefix : forall D n k,
  D >= 1 -> n >= 0 ->
  k <= D ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 k) =
  valid_R1R0_entry_number (D - k) (3^k * n + (3^k - 1) / 2).
Proof.
intros D n k HD Hn Hk.
revert D n HD Hn Hk.
induction k as [|k' IHK]; intros D n HD Hn Hk.
-
simpl.
rewrite Nat.sub_0_r.
unfold sequence_end. simpl.
assert (H_arith: n + 0 + 0 = n) by lia.
rewrite H_arith.
reflexivity.
-
assert (Hk'_bound: k' <= D - 1) by lia.
change (repeat_R1R0 (S k')) with ([R1; R0] ++ repeat_R1R0 k').
rewrite sequence_end_app.
destruct (Nat.eq_dec D 1) as [HD1 | HD1].
+
subst D.
assert (k'_zero: k' = 0) by lia.
subst k'.
simpl.
pose proof (R1R0_pattern_closure 1 n (le_n 1) (Nat.le_0_l n)) as HR1R0.
rewrite HR1R0.
unfold sequence_end. simpl.
replace (1 * (3 * n + 1) + 0) with (3 * n + 1) by lia.
reflexivity.
+
assert (HDge2: D >= 2) by lia.
pose proof (R1R0_pattern_closure D n HD (Nat.le_0_l n)) as HR1R0.
rewrite HR1R0.
assert (H_D_minus_1_ge_1: D - 1 >= 1) by lia.
assert (H_3n_plus_1_ge_0: 3 * n + 1 >= 0) by lia.
assert (H_k'_le_D_minus_1: k' <= D - 1) by lia.
pose proof (IHK (D - 1) (3 * n + 1) H_D_minus_1_ge_1 H_3n_plus_1_ge_0 H_k'_le_D_minus_1) as IH_applied.
rewrite IH_applied.
assert (H_arith: D - S k' = (D - 1) - k') by lia.
rewrite H_arith.
f_equal.
symmetry.
apply arithmetic_identity_for_R1R0; lia.
Qed.

(* R1R0 pattern closure arithmetic identity *)
Lemma R1R0_closure_arithmetic_identity : forall k n,
  k >= 1 -> n >= 1 ->
  3 * (3^k * n + (3^k - 1) / 2) + 1 = 3^(S k) * n + (3^(S k) - 1) / 2.
Proof.
intros k n Hk Hn.
destruct (pow3_minus1_even k) as [y Hy].
assert (Hdiv: (3^k - 1) / 2 = y).
{ rewrite Hy. apply twice_div. }
assert (H3k: 3^k = 2*y + 1).
{ assert (H_ge1: 3^k >= 1) by apply pow3_ge1; lia. }
rewrite Hdiv, H3k.
rewrite pow3_expand.
rewrite H3k.
assert (H_rhs: (3 * (2*y + 1) - 1) / 2 = 3*y + 1).
{ assert (H_calc: 3 * (2*y + 1) - 1 = 2 * (3*y + 1)) by lia.
rewrite H_calc; apply twice_div. }
rewrite H_rhs. ring.
Qed.

(* R1R0 entry numbers are always odd *)
Lemma valid_R1R0_entry_number_odd : forall d n,
  d >= 1 -> n >= 0 ->
  Nat.even (valid_R1R0_entry_number d n) = false.
Proof.
intros d n Hd Hn.
destruct (valid_R1R0_entry_number_properties d n Hd Hn) as [_ Hodd].
exact Hodd.
Qed.

(* Appending a pair to the end of repeat_R1R0 equals S times repeat *)
Lemma repeat_R1R0_snoc : forall k,
  repeat_R1R0 k ++ [R1; R0] = repeat_R1R0 (S k).
Proof.
induction k; simpl; auto.
rewrite IHk. reflexivity.
Qed.

(* For R1R0 entry numbers, build_k_steps generates k pairs of R1R0 operations *)
Lemma build_k_steps_on_valid_R1R0_prefix_simple : forall D n k,
  D >= 1 -> n >= 0 ->
  k <= D ->
  build_k_steps (valid_R1R0_entry_number D n) k = repeat_R1R0 k.
Proof.
intros D n k HD Hn Hk.
revert D n HD Hn Hk.
induction k as [|k' IHK]; intros D n HD Hn Hk.
+ simpl; reflexivity.
+ assert (Hk'leD: k' <= D) by lia.
   specialize (IHK D n HD Hn Hk'leD).
   (* Two cases for n: 0 or >=1; when n=0 and k'>=0 we still rely on parity = odd for first step, but
      sequence_end_valid_R1R0_prefix lemma already covers n>=0. *)
   assert (Hentry_valid: valid_input (valid_R1R0_entry_number D n)) by (apply valid_R1R0_entry_number_properties; lia).
   rewrite (build_k_steps_Sn (valid_R1R0_entry_number D n) k'); [ | exact Hentry_valid ].
   simpl.
   rewrite IHK.
   assert (Hodd_entry: Nat.even (sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 k')) = false).
   { destruct (Nat.eq_dec k' 0) as [Z|NZ].
     - subst k'. simpl.
       destruct (valid_R1R0_entry_number_properties D n HD Hn) as [_ Hodd]; exact Hodd.
     - assert (Hk'pos: k' >= 1) by lia.
       (* Need to rewrite to a smaller depth entry number whose parameter is 3*n+1 >=1 even when n=0 *)
       pose proof (sequence_end_valid_R1R0_prefix D n k' HD Hn Hk'leD) as Hseq.
       rewrite Hseq.
      assert (HresDepth: D - k' >= 1) by lia.
      apply valid_R1R0_entry_number_odd; [exact HresDepth | lia]. }
   rewrite Hodd_entry.
   rewrite repeat_R1R0_snoc.
   reflexivity.
Qed.

(* For R1R0 entry numbers, build_k_steps generates D pairs of R1R0 operations (fully expanded) *)
Lemma build_k_steps_on_valid_R1R0 : forall D n,
  D >= 1 -> n >= 0 ->
  build_k_steps (valid_R1R0_entry_number D n) D = repeat_R1R0 D.
Proof.
intros D n HD Hn.
apply build_k_steps_on_valid_R1R0_prefix_simple; auto; lia.
Qed.
