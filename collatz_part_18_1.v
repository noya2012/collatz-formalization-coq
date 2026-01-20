Load "collatz_part_18.v".
(* Load "collatz_part_16_2.v".*)

(*  定理R1R0到R0R0的闭包  *)
Theorem R1R0_to_R0R0_closure :
  forall (d : nat) (n : nat),
  d >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number d n in
  let Send := sequence_end m (repeat_R1R0 d) in
  is_even Send ->
  exists (d' : nat) (n' : nat),
    d' >= 1 /\ is_odd n' /\ n' >= 1 /\
    Send = valid_R0R0_entry_number d' n' /\
    sequence_end (valid_R0R0_entry_number d' n') (repeat_R0 d') = n'.
Proof.
intros d n Hd Hn.
intros Heven_Send.
pose proof (valid_R1R0_entry_number_properties d n Hd Hn) as [Hm_ge1 Hm_odd].
pose proof (odd_leads_R1R0_then_R0_pattern (valid_R1R0_entry_number d n) d n Hm_ge1 Hd Hn eq_refl) as Hpattern.
destruct Hpattern as [Send' [Hseq_eq [Heven_Send' [Hbounds [Hbuild Hunique]]]]].
assert (HSend_ge1 : Send' >= 1).
{ destruct Hbounds as [Hlower [Hupper Hmin]].
assert (Hthreepow_minus_ge1 : 3 ^ d - 1 >= 1).
{ assert (Hthreepow_minus_ge2 : 3 ^ d - 1 >= 2).
{ replace 2 with (3 ^ 1 - 1) by (simpl; reflexivity).
apply Nat.sub_le_mono_r.
apply Nat.pow_le_mono_r; lia. }
lia. }
apply (Nat.le_trans _ (3 ^ d - 1)); [exact Hthreepow_minus_ge1 | exact Hmin]. }
pose proof (build_k_steps_numeric_canonical Send' HSend_ge1) as Hcanon.
destruct Hcanon as
[ [d0 [n0 [Hd0 [Hn0 [HSendDef [Hbuild0 [Hrange0 Huniq0]]]]]]] |
[d0 [n0 [Hd0 [Hn0 [Hodd0 [HSendDef [Hbuild0 [Hseq0 Huniq1]]]]]]]] ].
-
pose proof (valid_R1R0_entry_number_is_odd d0 n0 Hd0 Hn0) as HoddSend.
unfold is_odd in HoddSend.
rewrite <- HSendDef in HoddSend.
unfold is_even in Heven_Send'.
rewrite HoddSend in Heven_Send'; discriminate.
-
exists d0, n0.
split; [exact Hd0|].
split; [exact Hodd0|].
split; [exact Hn0|].
split.
+
unfold Heven_Send.
rewrite Hseq_eq.
exact HSendDef.
+
rewrite <- HSendDef.
exact Hseq0.
Qed.

(*  R0到R1R0的闭包  *)
Theorem R0R0_to_R1R0_reverse : forall (d' : nat) (n' : nat),
  d' >= 1 -> is_odd n' -> n' >= 1 ->
  exists (d : nat) (n : nat),
    d >= 1 /\ n >= 0 /\
    n' = valid_R1R0_entry_number d n /\
    is_odd (valid_R1R0_entry_number d n).
Proof.
intros d' n' Hd' Hodd_n' Hn'.
set (m := valid_R0R0_entry_number d' n').
pose proof (valid_R0R0_entry_number_properties d' n' Hd' Hn') as [Hm_ge1 Heven_m].
assert (Hentry_R0R0 : R0R0_entry m d' n').
{
unfold R0R0_entry.
split.
- unfold m.
assert (Hm_ge1' : valid_R0R0_entry_number d' n' >= 1).
{ lia. }
exact Hm_ge1'.
- split; [exact Hd'|].
split; [exact Hn'|].
split; [exact Hodd_n'|].
reflexivity.
}
pose proof (next_entry_from_R0R0 m d' n' Hentry_R0R0) as Hnext.
destruct Hnext as [Send [d [n [Hseq_eq [Hodd_Send [Hentry_R1R0 Hbuild]]]]]].
unfold R1R0_entry in Hentry_R1R0.
destruct Hentry_R1R0 as [HSend [Hd [Hn Hrepr]]].
exists d, n.
split; [exact Hd|].
split; [exact Hn|].
split.
-
rewrite <- Hrepr.
pose proof (repeat_R0_output_reaches_one d' n' Hd' Hn') as Hseq_end_eq.
unfold m in Hseq_eq, Hseq_end_eq.
rewrite Hseq_end_eq in Hseq_eq.
exact Hseq_eq.
-
rewrite <- Hrepr.
exact Hodd_Send.
Qed.


(*  从 R1R0 分支出发，经过 R0R0 分支，再回到 R1R0 分支*)
Theorem R1R0_full_cycle_step :
  forall (d : nat) (n : nat),
  d >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number d n in
  let Send := sequence_end m (repeat_R1R0 d) in
  is_even Send ->
  exists (d' d'' : nat) (n' n'' : nat),
    d' >= 1 /\ is_odd n' /\ n' >= 1 /\
    Send = valid_R0R0_entry_number d' n' /\
    sequence_end Send (repeat_R0 d') = n' /\
    d'' >= 1 /\ n'' >= 0 /\
    n' = valid_R1R0_entry_number d'' n'' /\
    is_odd (valid_R1R0_entry_number d'' n'').
Proof.
intros d n Hd Hn m Send Heven_Send.
pose proof (R1R0_to_R0R0_closure d n Hd Hn Heven_Send) as Hclosure.
destruct Hclosure as [d' [n' [Hd' [Hodd_n' [Hn' [HSendDef Hseq_end']]]]]].
pose proof (R0R0_to_R1R0_reverse d' n' Hd' Hodd_n' Hn') as Hreverse.
destruct Hreverse as [d'' [n'' [Hd'' [Hn'' [Hn'_repr Hodd_repr]]]]].
exists d', d'', n', n''.
split; [exact Hd'|].
split; [exact Hodd_n'|].
split; [exact Hn'|].
split; [unfold Send; exact HSendDef|].
split; [unfold Send; transitivity (sequence_end (valid_R0R0_entry_number d' n') (repeat_R0 d')); [rewrite <- HSendDef; reflexivity | exact Hseq_end']|].
split; [exact Hd''|].
split; [exact Hn''|].
split; [exact Hn'_repr|].
exact Hodd_repr.
Qed.

(* R0R0 分支也有对称的完整循环步骤 *)
Theorem R0R0_full_cycle_step :
  forall (d : nat) (n : nat),
  d >= 1 -> n >= 1 -> is_odd n ->
  let m := valid_R0R0_entry_number d n in
  let Send := sequence_end m (repeat_R0 d) in
  (* Send = n，是奇数 *)
  exists (d' d'' : nat) (n' n'' : nat),
    (* 第一步：R0R0 链执行后进入 R1R0 分支 *)
    d' >= 1 /\ n' >= 0 /\
    Send = valid_R1R0_entry_number d' n' /\
    is_odd (valid_R1R0_entry_number d' n') /\
    (* 第二步：R1R0 链执行后 Send' 是偶数，可回到 R0R0 分支 *)
    d'' >= 1 /\ is_odd n'' /\ n'' >= 1 /\
    sequence_end (valid_R1R0_entry_number d' n') (repeat_R1R0 d') =
      valid_R0R0_entry_number d'' n''.
Proof.
intros d n Hd Hn Hodd_n m Send.
pose proof (repeat_R0_output_reaches_one d n Hd Hn) as Hseq_end.
assert (HSend_eq : Send = n) by exact Hseq_end.
pose proof (R0R0_to_R1R0_reverse d n Hd Hodd_n Hn) as Hreverse.
destruct Hreverse as [d' [n' [Hd' [Hn' [Hn_repr Hodd_repr]]]]].
assert (Heven_output : is_even (sequence_end (valid_R1R0_entry_number d' n') (repeat_R1R0 d'))).
{
pose proof (repeat_R1R0_output_closed_form_no_div d' n' Hd' Hn') as Hclosed.
unfold is_even.
rewrite Hclosed.
pose proof (pow3_minus1_even d') as [y Hy].
rewrite Hy.
replace (2 * 3 ^ d' * n' + 2 * y) with (2 * (3 ^ d' * n' + y)) by ring.
rewrite Nat.even_mul.
rewrite Nat.even_2.
simpl.
reflexivity. }
pose proof (R1R0_to_R0R0_closure d' n' Hd' Hn' Heven_output) as Hclosure.
destruct Hclosure as [d'' [n'' [Hd'' [Hodd_n'' [Hn'' [HSendDef Hseq_end']]]]]].
exists d', d'', n', n''.
repeat split; try assumption.
- rewrite HSend_eq. exact Hn_repr.
Qed.

(*  循环状态与迭代关系  *)

Record cycle_state := {
  cs_branch : bool;
  cs_d : nat;
  cs_n : nat
}.

(*  构造循环状态  *)
Definition mk_cycle_state (b : bool) (d n : nat) : cycle_state :=
  {| cs_branch := b; cs_d := d; cs_n := n |}.

(*  循环状态的有效性  *)
Definition valid_cycle_state (s : cycle_state) : Prop :=
  match cs_branch s with
  | true =>
      cs_d s >= 1 /\
      cs_n s >= 0 /\
      is_even
        (sequence_end (valid_R1R0_entry_number (cs_d s) (cs_n s))
                      (repeat_R1R0 (cs_d s)))
  | false =>
      cs_d s >= 1 /\
      cs_n s >= 1 /\
      is_odd (cs_n s)
  end.
(*  循环步骤关系  *)
Inductive cycle_step : cycle_state -> cycle_state -> Prop :=
| cycle_step_from_R1R0 :
    forall d n d' d'' n' n'',
      d >= 1 ->
      n >= 0 ->
      let m := valid_R1R0_entry_number d n in
      let Send := sequence_end m (repeat_R1R0 d) in
      is_even Send ->
      d' >= 1 ->
      is_odd n' ->
      n' >= 1 ->
      Send = valid_R0R0_entry_number d' n' ->
      sequence_end Send (repeat_R0 d') = n' ->
      d'' >= 1 ->
      n'' >= 0 ->
      n' = valid_R1R0_entry_number d'' n'' ->
      is_odd (valid_R1R0_entry_number d'' n'') ->
      cycle_step (mk_cycle_state true d n) (mk_cycle_state true d'' n'')
| cycle_step_from_R0R0 :
    forall d n d' d'' n' n'',
      d >= 1 ->
      n >= 1 ->
      is_odd n ->
      let m := valid_R0R0_entry_number d n in
      let Send := sequence_end m (repeat_R0 d) in
      d' >= 1 ->
      n' >= 0 ->
      Send = valid_R1R0_entry_number d' n' ->
      is_odd (valid_R1R0_entry_number d' n') ->
      is_even (sequence_end (valid_R1R0_entry_number d' n') (repeat_R1R0 d')) ->
      d'' >= 1 ->
      is_odd n'' ->
      n'' >= 1 ->
      sequence_end (valid_R1R0_entry_number d' n') (repeat_R1R0 d') =
        valid_R0R0_entry_number d'' n'' ->
      cycle_step (mk_cycle_state false d n) (mk_cycle_state false d'' n'').

(*  循环步骤的多步关系  *)
Inductive cycle_steps : nat -> cycle_state -> cycle_state -> Prop :=
| cycle_steps_zero :
    forall s, cycle_steps 0 s s
| cycle_steps_succ :
    forall k s1 s2 s3,
      cycle_step s1 s2 ->
      cycle_steps k s2 s3 ->
      cycle_steps (S k) s1 s3.

(*  循环步骤的度量  *)
Definition cycle_measure (s : cycle_state) : nat :=
  match cs_branch s with
  | true =>
      sequence_end (valid_R1R0_entry_number (cs_d s) (cs_n s))
                   (repeat_R1R0 (cs_d s))
  | false =>
      valid_R0R0_entry_number (cs_d s) (cs_n s)
  end.

(*  循环步骤的收敛性  *)
Theorem cycle_steps_convergence_R1R0 :
  forall (d : nat) (n : nat),
    d >= 1 ->
    n >= 0 ->
    valid_cycle_state (mk_cycle_state true d n) ->
    exists (k : nat) (s_final : cycle_state),
      cycle_steps k (mk_cycle_state true d n) s_final /\
      cs_branch s_final = true.

Proof.
intros d n Hd Hn Hvalid.
destruct Hvalid as [Hd_valid [Hn_valid Heven_Send]].
pose proof (R1R0_full_cycle_step d n Hd_valid Hn_valid Heven_Send) as Hcycle.
destruct Hcycle as [d' [d'' [n' [n'' [Hd' [Hodd_n' [Hn' [HSend_def [Hseq_end [Hd'' [Hn'' [Hn'_repr Hodd_repr]]]]]]]]]]]].
exists 1, (mk_cycle_state true d'' n'').
split.
{
apply cycle_steps_succ with (s2 := mk_cycle_state true d'' n'').
- eapply cycle_step_from_R1R0.
+ exact Hd_valid.
+ exact Hn_valid.
+ exact Heven_Send.
+ exact Hd'.
+ exact Hodd_n'.
+ exact Hn'.
+ exact HSend_def.
+ exact Hseq_end.
+ exact Hd''.
+ exact Hn''.
+ exact Hn'_repr.
+ exact Hodd_repr.
- apply cycle_steps_zero.
}
- reflexivity.
Qed.

(*  R0R0 分支收敛性定理  *)
Theorem cycle_steps_convergence_R0R0 :
  forall (d : nat) (n : nat),
    d >= 1 ->
    n >= 1 ->
    valid_cycle_state (mk_cycle_state false d n) ->
    exists (k : nat) (s_final : cycle_state),
      cycle_steps k (mk_cycle_state false d n) s_final /\
      cs_branch s_final = false.

Proof.
intros d n Hd Hn Hvalid.
destruct Hvalid as [Hd_valid [Hn_valid Hodd_n]].
pose proof (R0R0_full_cycle_step d n Hd_valid Hn_valid Hodd_n) as Hcycle.
destruct Hcycle as (d' & d'' & n' & n'' & H).
destruct H as [Hd' [Hn' [HSend_def [Hodd_repr [Hd'' [Hodd_n'' [Hn'' Hseq_end]]]]]]].
assert (Heven_output : is_even (sequence_end (valid_R1R0_entry_number d' n') (repeat_R1R0 d'))).
{
pose proof (repeat_R1R0_output_closed_form_no_div d' n' Hd' Hn') as Hclosed.
unfold is_even.
rewrite Hclosed.
pose proof (pow3_minus1_even d') as [y Hy].
rewrite Hy.
replace (2 * 3 ^ d' * n' + 2 * y) with (2 * (3 ^ d' * n' + y)) by ring.
rewrite Nat.even_mul.
rewrite Nat.even_2.
simpl.
reflexivity. }
exists 1, (mk_cycle_state false d'' n'').
split.
{
apply cycle_steps_succ with (s2 := mk_cycle_state false d'' n'').
- eapply cycle_step_from_R0R0.
+ exact Hd_valid.
+ exact Hn.
+ exact Hodd_n.
+ exact Hd'.
+ exact Hn'.
+ exact HSend_def.
+ exact Hodd_repr.
+ exact Heven_output.
+ exact Hd''.
+ exact Hodd_n''.
+ exact Hn''.
+ exact Hseq_end.
- apply cycle_steps_zero.
}
- reflexivity.
Qed.

(*  循环状态可达性定理  *)
Theorem cycle_state_reachability :
  forall (s : cycle_state),
    valid_cycle_state s ->
    exists (k : nat) (s_final : cycle_state),
      cycle_steps k s s_final /\
      cs_branch s_final = cs_branch s.
Proof.
intros s Hvalid.
destruct s as [b d n].
simpl in Hvalid.
destruct b.
-
destruct Hvalid as [Hd [Hn Heven]].
assert (Hn_ge0 : n >= 0).
{ apply le_0_n. }
assert (Hvalid_mk : valid_cycle_state (mk_cycle_state true d n)).
{ simpl; repeat split; assumption. }
destruct (cycle_steps_convergence_R1R0 d n Hd Hn_ge0 Hvalid_mk)
as [k [s_final [Hsteps Hbranch]]].
exists k, s_final.
split; [exact Hsteps|].
simpl; exact Hbranch.
-
destruct Hvalid as [Hd [Hn Hodd]].
assert (Hvalid_mk : valid_cycle_state (mk_cycle_state false d n)).
{ simpl; repeat split; assumption. }
destruct (cycle_steps_convergence_R0R0 d n Hd Hn Hvalid_mk)
as [k [s_final [Hsteps Hbranch]]].
exists k, s_final.
split; [exact Hsteps|].
simpl; exact Hbranch.
Qed.

(*  规范链的R0操作优势定理  *)
Theorem canonical_R0_advantage :
  forall (s : cycle_state),
    valid_cycle_state s ->
    let ops := canonical_chain (cs_branch s) (cs_d s) in
    fst (count_operations ops) > snd (count_operations ops) /\
    fst (count_operations ops) - snd (count_operations ops) =
      (if cs_branch s then 1 else cs_d s).
Proof.
intros s Hvalid.
destruct s as [branch d n].
simpl in *.
destruct branch.
- destruct Hvalid as [Hd _].
pose proof (canonical_chain_R0_advantage true d Hd) as Hadv.
unfold canonical_chain.
simpl in Hadv.
destruct (count_operations (repeat_R1R0 d ++ [R0])) as [r0s r1s] eqn:Hcount.
destruct Hadv as [Hgt Heq].
split.
+ unfold fst, snd.
exact Hgt.
+ unfold fst, snd.
exact Heq.
- destruct Hvalid as [Hd _].
pose proof (canonical_chain_R0_advantage false d Hd) as Hadv.
unfold canonical_chain.
simpl in Hadv.
destruct (count_operations (repeat_R0 d ++ [R1; R0])) as [r0s r1s] eqn:Hcount.
destruct Hadv as [Hgt Heq].
split.
+ unfold fst, snd.
exact Hgt.
+ unfold fst, snd.
exact Heq.
Qed.

(*  循环步性质封装  *)
Lemma valid_cycle_state_cycle_step :
  forall (s : cycle_state),
    valid_cycle_state s ->
    exists (s' : cycle_state),
      cycle_step s s' /\ cs_branch s' = cs_branch s.
Proof.
intros [branch d n] Hvalid.
simpl in Hvalid.
destruct branch.
- destruct Hvalid as [Hd [Hn Heven]].
pose proof (R1R0_full_cycle_step d n Hd Hn Heven)
as [d' [d'' [n' [n'' [Hd' [Hodd_n' [Hn' [HSendDef [Hseq_end [Hd'' [Hn'' [Hn'_repr Hodd_repr]]]]]]]]]]]].
exists (mk_cycle_state true d'' n'').
split.
+ refine (cycle_step_from_R1R0 _ _ _ _ _ _ Hd Hn Heven Hd' Hodd_n' Hn' HSendDef Hseq_end Hd'' Hn'' Hn'_repr Hodd_repr).
+ reflexivity.
- destruct Hvalid as [Hd [Hn Hodd]].
pose proof (R0R0_full_cycle_step d n Hd Hn Hodd)
as [d' [d'' [n' [n'' [Hd' [Hn' [HSend_def [Hodd_repr [Hd'' [Hodd_n'' [Hn'' Hseq_end]]]]]]]]]]].
pose proof (repeat_R1R0_output_closed_form_no_div d' n' Hd' Hn') as Hclosed.
assert (Heven_output : is_even (sequence_end (valid_R1R0_entry_number d' n') (repeat_R1R0 d'))).
{ unfold is_even. rewrite Hclosed.
pose proof (pow3_minus1_even d') as [y Hy].
rewrite Hy.
replace (2 * 3 ^ d' * n' + 2 * y) with (2 * (3 ^ d' * n' + y)) by ring.
rewrite Nat.even_mul, Nat.even_2. simpl. reflexivity. }
exists (mk_cycle_state false d'' n'').
split.
+ refine (cycle_step_from_R0R0 _ _ _ _ _ _ Hd Hn Hodd Hd' Hn' HSend_def Hodd_repr Heven_output Hd'' Hodd_n'' Hn'' Hseq_end).
+ reflexivity.
Qed.

(* 对于任何有效的循环状态，存在一个有限步数k，使得经过k次循环步后，状态仍然保持在同一分支 *)
Theorem chain_characterization_with_advantage :
  (forall m, m mod 6 = 2 ->
     exists d n, d >= 1 /\ n >= 0 /\
     m = sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) /\
     let '(r0s, r1s) := count_operations (canonical_chain true d) in
     r0s = d + 1 /\ r1s = d /\ r0s <= 2 * r1s) /\
  (forall m, m mod 2 = 1 ->
     exists d n, d >= 1 /\ n >= 1 /\ is_odd n /\
     m = sequence_end (valid_R0R0_entry_number d n) (repeat_R0 d) /\
     let '(r0s, r1s) := count_operations (canonical_chain false d) in
     r0s = d + 1 /\ r1s = 1 /\ r0s >= 2 * r1s).
Proof.
split.
- intros m Hmod.
destruct (R1R0_output_set_iff m) as [_ H].
destruct (H Hmod) as [d [n [Hd [Hn Heq]]]].
exists d, n.
split; [exact Hd|].
split; [exact Hn|].
split; [exact Heq|].
destruct (count_operations (canonical_chain true d)) as [r0s r1s] eqn:Hcount.
pose proof (count_operations_canonical_chain true d Hd) as Hcanon.
rewrite Hcount in Hcanon.
injection Hcanon as Hr0 Hr1.
split; [exact Hr0|].
split; [exact Hr1|].
rewrite Hr0, Hr1; lia.
- intros m Hmod.
destruct m as [|m'].
{ simpl in Hmod. discriminate. }
exists 1, (S m').
split; [lia|].
split; [lia|].
split; [apply mod2_eq1_implies_is_odd; exact Hmod|].
split.
{ apply eq_sym. apply R0R0_output_exact_n; lia. }
destruct (count_operations (canonical_chain false 1)) as [r0s r1s] eqn:Hcount.
pose proof (count_operations_canonical_chain false 1 (le_n 1)) as Hcanon.
rewrite Hcount in Hcanon.
injection Hcanon as Hr0 Hr1.
split; [exact Hr0|].
split; [exact Hr1|].
rewrite Hr0, Hr1; lia.
Qed.



(*  R1R0链比例公式 *)
Theorem R1R0_chain_ratio_formula : forall d,
  d >= 1 ->
  let '(r0s, r1s) := count_operations (canonical_chain true d) in
  r0s / r1s = (d + 1) / d /\
  r0s = r1s + 1.
Proof.
intros d Hd.
pose proof (count_operations_canonical_chain true d Hd) as Hcount.
destruct (count_operations (canonical_chain true d)) as [r0s r1s].
injection Hcount as Hr0 Hr1.
rewrite Hr0, Hr1.
split; [reflexivity|lia].
Qed.

(*  R0链比例公式 *)
Theorem R0_chain_ratio_formula : forall d,
  d >= 1 ->
  let '(r0s, r1s) := count_operations (canonical_chain false d) in
  r0s / r1s = d + 1 /\
  r0s = r1s * (d + 1).
Proof.
intros d Hd.
pose proof (count_operations_canonical_chain false d Hd) as Hcount.
destruct (count_operations (canonical_chain false d)) as [r0s r1s].
injection Hcount as Hr0 Hr1.
rewrite Hr0, Hr1.
split; [rewrite Nat.div_1_r; reflexivity|ring].
Qed.

(*  统一比例公式  *)
Theorem unified_chain_ratio_formula : forall b d,
  d >= 1 ->
  let '(r0s, r1s) := count_operations (canonical_chain b d) in
  match b with
  | true => r0s = d + 1 /\ r1s = d /\ r0s = r1s + 1
  | false => r0s = d + 1 /\ r1s = 1 /\ r0s = (d + 1) * r1s
  end.
Proof.
intros b d Hd.
destruct b.
- pose proof (count_operations_canonical_chain true d Hd) as Hcount.
rewrite Hcount. repeat split; lia.
- pose proof (count_operations_canonical_chain false d Hd) as Hcount.
rewrite Hcount. repeat split; lia.
Qed.

(*  比例优势分析  *)
Theorem R0_advantage_ratio_analysis : forall b d,
  d >= 1 ->
  let '(r0s, r1s) := count_operations (canonical_chain b d) in
  r0s > r1s /\
  (if b then r0s <= 2 * r1s else r0s >= 2 * r1s) /\
  r0s - r1s = (if b then 1 else d).
Proof.
intros b d Hd.
destruct b.
- pose proof (count_operations_canonical_chain true d Hd) as Hcount.
rewrite Hcount. repeat split; lia.
- pose proof (count_operations_canonical_chain false d Hd) as Hcount.
rewrite Hcount. repeat split; lia.
Qed.

(*  序列组合的比例公式  *)
Theorem total_operations_ratio_formula : forall chains,
  chains <> nil ->
  (forall bd, In bd chains -> let '(b, d) := bd in d >= 1) ->
  let total_ops := chains_to_sequence chains in
  let '(total_r0s, total_r1s) := count_operations total_ops in
  let contributions := sum_contributions chains in
  total_r0s = total_r1s + contributions.
Proof.
intros chains Hnonempty Hvalid.
simpl.
destruct (count_operations (chains_to_sequence chains)) as [total_r0s total_r1s] eqn:Hops.
simpl.
pose proof (count_operations_chains_sequence chains) as Hcount.
rewrite Hops in Hcount.
simpl in Hcount.
rewrite Nat.add_comm in Hcount.
exact Hcount.
Qed.

(* pattern_toggle_deterministic : 确定性模式切换定理 *)
Theorem pattern_toggle_deterministic :
  (forall m, m mod 6 = 2 ->
     exists d n d' n',
       d >= 1 /\ n >= 0 /\
       d' >= 1 /\ n' >= 1 /\ is_odd n' /\
       m = sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) /\
       valid_input m /\
       m = valid_R0R0_entry_number d' n' /\
       let next_m := sequence_end m (repeat_R0 d') in
       next_m mod 2 = 1) /\
  (forall m, m mod 2 = 1 ->
     exists d n d' n',
       d >= 1 /\ n >= 1 /\ is_odd n /\
       d' >= 1 /\ n' >= 0 /\
       m = sequence_end (valid_R0R0_entry_number d n) (repeat_R0 d) /\
       valid_input m /\
       m = valid_R1R0_entry_number d' n' /\
       let next_m := sequence_end m (repeat_R1R0 d') in
       next_m mod 6 = 2).
Proof.
pose proof chain_characterization_with_advantage as [HR1 HR0].
split.
- intros m Hmod6.
specialize (HR1 m Hmod6).
destruct HR1 as [d [n [Hd [Hn [Hm_end _]]]]].
pose proof (valid_R1R0_entry_number_properties d n Hd Hn) as [Hentry_ge _].
assert (Hentry_valid : valid_input (valid_R1R0_entry_number d n)).
{ unfold valid_input. exact Hentry_ge. }
destruct (R1R0_entry_number_produces_repeat d n Hd Hn) as [Hseq_repeat _].
assert (Hvalid_m : valid_input m).
{ rewrite Hm_end. apply sequence_end_valid; [exact Hentry_valid | exact Hseq_repeat]. }
assert (HSend_even :
is_even (sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d))).
{
destruct (repeat_R1R0_output_even d n Hd Hn) as [k Hk].
rewrite Hk. apply even_2x.
}
destruct (R1R0_to_R0R0_closure d n Hd Hn HSend_even)
as [d' [n' [Hd' [Hodd_n' [Hn'_ge1 [Hsend_eq Hnext_eq]]]]]].
assert (Hm_is_R0_entry : m = valid_R0R0_entry_number d' n').
{ rewrite Hm_end. rewrite <- Hsend_eq. reflexivity. }
assert (Hnext_value : sequence_end m (repeat_R0 d') = n').
{ rewrite Hm_is_R0_entry. exact Hnext_eq. }
exists d, n, d', n'.
repeat split.
+ exact Hd.
+ exact Hn.
+ exact Hd'.
+ exact Hn'_ge1.
+ exact Hodd_n'.
+ exact Hm_end.
+ exact Hvalid_m.
+ exact Hm_is_R0_entry.
+ change ((sequence_end m (repeat_R0 d')) mod 2 = 1).
rewrite Hnext_value.
unfold is_odd in Hodd_n'.
assert (Nat.odd n' = true) as Hodd_bool.
{ unfold Nat.odd. rewrite Hodd_n'. simpl. reflexivity. }
apply Nat.odd_spec in Hodd_bool as [k Hk].
rewrite Hk.
rewrite Nat.add_comm.
rewrite Nat.mul_comm.
rewrite Nat.mod_add by lia.
simpl. reflexivity.
- intros m Hmod2.
assert (Hnonzero : m <> 0).
{ intros H0. rewrite H0 in Hmod2. simpl in Hmod2. discriminate Hmod2. }
assert (Hm_ge1 : 1 <= m) by lia.
assert (Hodd_m : is_odd m) by (apply mod2_eq1_implies_is_odd; assumption).
assert (Hend_eq : m = sequence_end (valid_R0R0_entry_number 1 m) (repeat_R0 1)).
{ symmetry. apply repeat_R0_output_reaches_one; lia. }
assert (Hvalid_m : valid_input m).
{ unfold valid_input. exact Hm_ge1. }
destruct (R0R0_to_R1R0_reverse 1 m (Nat.le_refl 1) Hodd_m Hm_ge1)
as [d' [n' [Hd' [Hn'_ge0 [Heq_entry _]]]]].
exists 1, m, d', n'.
repeat split.
+ lia.
+ exact Hm_ge1.
+ exact Hodd_m.
+ exact Hd'.
+ exact Hn'_ge0.
+ exact Hend_eq.
+ exact Hvalid_m.
+ exact Heq_entry.
+ change ((sequence_end m (repeat_R1R0 d')) mod 6 = 2).
rewrite Heq_entry.
apply R1R0_output_mod6; [exact Hd' | exact Hn'_ge0].
Qed.

(* R0 advantage for the concatenated canonical chains. *)
Theorem mod62_R0advantage :
  forall m0,
    m0 mod 6 = 2 ->
    exists d0 n0 d1 n1 m1 m2,
      let chains := [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)] in
      valid_chains_condition chains /\
      chains_R0_advantage chains /\
      m2 mod 6 = 2 /\
      sum_contributions (extract_simple_chains chains) = d0 + 1.
Proof.
intros m0 Hm0.
pose proof pattern_toggle_deterministic as [HtoOdd _].
specialize (HtoOdd m0 Hm0).
destruct HtoOdd as
[d [n [d0 [n0
[Hd [Hn [Hd0 [Hn0 [Hodd_n0 [Hm0_as_R1R0out [Hvalid_m0 [Hm0_as_R0R0_entry Hm1_mod2]]]]]]]]]]]].
set (m1 := sequence_end m0 (repeat_R0 d0)).
assert (Hm1_eq_n0 : m1 = n0).
{
unfold m1.
rewrite Hm0_as_R0R0_entry.
apply repeat_R0_output_reaches_one; lia.
}
assert (Hodd_m1 : is_odd m1).
{ rewrite Hm1_eq_n0. exact Hodd_n0. }
assert (Hm1_ge1 : m1 >= 1).
{ rewrite Hm1_eq_n0. exact Hn0. }
destruct (R0R0_to_R1R0_reverse 1 m1 (Nat.le_refl 1) Hodd_m1 Hm1_ge1)
as [d1 [n1 [Hd1 [Hn1 [Hm1_as_R1R0_entry _]]]]].
set (m2 := sequence_end m1 (repeat_R1R0 d1)).
assert (Hm2_mod6' : m2 mod 6 = 2).
{
unfold m2.
rewrite Hm1_as_R1R0_entry.
apply R1R0_output_mod6; [exact Hd1 | exact Hn1].
}
exists d0, n0, d1, n1, m1, m2.
cbv beta.
set (chains := [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)]).
change (valid_chains_condition chains /\
chains_R0_advantage chains /\
m2 mod 6 = 2 /\
sum_contributions (extract_simple_chains chains) = d0 + 1).
assert (Hchains_nonempty : chains <> nil).
{ unfold chains; discriminate. }
assert (Hchains_valid : forall bdnds,
In bdnds chains ->
let '(b, dX, nX, mX, SendX) := bdnds in
valid_chain_sequence_condition b dX nX mX SendX).
{
intros bdnds Hin.
unfold chains in Hin.
simpl in Hin.
destruct Hin as [Hin | [Hin | []]];
subst bdnds.
-
unfold valid_chain_sequence_condition.
split; [exact Hd0|].
right.
split; [reflexivity|].
split; [exact Hn0|].
split; [exact Hodd_n0|].
split; [exact Hm0_as_R0R0_entry|].
split; [unfold m1; reflexivity|].
exact Hodd_m1.
-
unfold valid_chain_sequence_condition.
split; [exact Hd1|].
left.
split; [reflexivity|].
split; [exact Hn1|].
split; [exact Hm1_as_R1R0_entry|].
split; [unfold m2; reflexivity|].
assert (His_even_m2 : is_even (sequence_end (valid_R1R0_entry_number d1 n1) (repeat_R1R0 d1))).
{
destruct (repeat_R1R0_output_even d1 n1 Hd1 Hn1) as [k Hk].
rewrite Hk. apply even_2x.
}
unfold m2.
rewrite Hm1_as_R1R0_entry.
exact His_even_m2.
}
assert (Hcond : valid_chains_condition chains).
{
unfold valid_chains_condition.
split; [exact Hchains_nonempty|].
intros bdnds Hin.
exact (Hchains_valid bdnds Hin).
}
assert (Hadv : chains_R0_advantage chains).
{
unfold chains_R0_advantage.
apply (valid_chains_sequence_R0_advantage_corollary chains).
- exact Hchains_nonempty.
- intros bdnds Hin.
exact (Hchains_valid bdnds Hin).
}
split; [exact Hcond|].
split; [exact Hadv|].
split; [exact Hm2_mod6'|].
unfold chains. simpl. lia.
Qed.

(* Macro-step advantage: mod6=2 numbers gain at least 2 net-R0 advantage *)
Theorem mod62_macrostep_R0_net_advantage_ge_2 :
  forall m0,
    m0 mod 6 = 2 ->
    exists d0 n0 d1 n1 m1 m2,
      let chains := [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)] in
      valid_chains_condition chains /\
      chains_R0_advantage chains /\
      m2 mod 6 = 2 /\
      2 <= sum_contributions (extract_simple_chains chains).
Proof.
intros m0 Hm0.
destruct (mod62_R0advantage m0 Hm0)
as [d0 [n0 [d1 [n1 [m1 [m2 H]]]]]].
exists d0, n0, d1, n1, m1, m2.
cbn.
cbn in H.
destruct H as [Hcond [Hadv [Hm2 Hsum]]].
split; [exact Hcond|].
split; [exact Hadv|].
split; [exact Hm2|].
unfold valid_chains_condition in Hcond.
destruct Hcond as [_ Hall].
specialize (Hall (false, d0, n0, m0, m1)).
assert (Hin : In (false, d0, n0, m0, m1)
[(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)]).
{ simpl. left. reflexivity. }
specialize (Hall Hin).
simpl in Hall.
unfold valid_chain_sequence_condition in Hall.
destruct Hall as [Hd0 _].
lia.
Qed.

(* Any valid m can reach a mod6=2 orbit *)
Theorem direct_conversion_to_mod6_2_orbit :
  forall m,
    valid_input m ->
    exists k : nat, exists m_final : nat,
      m_final mod 6 = 2 /\
      exists ops : list CollatzOp,
        length ops = k /\
        valid_sequence ops m /\
        sequence_end m ops = m_final /\
        k <= 2 * (log2 m + 1).
Proof.
intros m Hvalid.
unfold valid_input in Hvalid.
destruct (complete_number_classification m Hvalid) as
[[Hodd [d [n [Hd [Hn Hm_entry]]]]] | [Heven _]].
-
set (ops := repeat_R1R0 d).
set (m_final := sequence_end m ops).
exists (length ops), m_final.
split.
+ subst m_final ops.
rewrite Hm_entry.
apply R1R0_output_mod6; assumption.
+ exists ops.
split; [reflexivity|].
split.
*
subst ops.
rewrite Hm_entry.
exact (proj1 (R1R0_entry_number_produces_repeat d n Hd Hn)).
* split.
--
subst m_final. reflexivity.
--
subst ops.
rewrite repeat_R1R0_length.
assert (Hd_le_log2m1 : d <= log2 (m + 1)).
{
apply (R1R0_entry_d_log2_bound m d n); try assumption.
}
assert (Hlog2m1_le : log2 (m + 1) <= log2 m + 1).
{
assert (Hle : m + 1 <= 2 * m) by lia.
apply Nat.le_trans with (log2 (2 * m)).
- apply log2_monotone. exact Hle.
- rewrite log2_mult_power2; [lia | lia].
}
apply Nat.mul_le_mono_pos_l; [lia|].
lia.
-
assert (Hm_ge2 : m >= 2).
{ apply even_ge_1_implies_ge_2; try lia. exact Heven. }
destruct (power2_odd_decomposition m Hm_ge2 Heven)
as [d [q [Hd_ge1 [Hq_ge1 [Hm_factor Hq_odd]]]]].
assert (Hm_as_R0R0 : m = valid_R0R0_entry_number d q).
{
unfold valid_R0R0_entry_number.
rewrite Nat.mul_comm.
exact Hm_factor.
}
assert (Hseq_R0 : valid_sequence (repeat_R0 d) m).
{
rewrite Hm_as_R0R0.
apply (proj1 (R0R0_entry_number_produces_repeat d q Hd_ge1 Hq_ge1)).
}
assert (Hend_R0 : sequence_end m (repeat_R0 d) = q).
{
rewrite Hm_as_R0R0.
apply (repeat_R0_output_reaches_one d q Hd_ge1 Hq_ge1).
}
assert (Hq_valid : q >= 1) by exact Hq_ge1.
destruct (complete_number_classification q Hq_valid) as [Hq_case | Hq_case].
+
destruct Hq_case as [Hq_is_odd [d1 [n1 [Hd1 [Hn1 Hq_entry]]]]].
clear Hq_is_odd.
set (ops2 := repeat_R1R0 d1).
set (ops := repeat_R0 d ++ ops2).
set (m_final := sequence_end m ops).
exists (length ops), m_final.
split.
*
subst m_final ops ops2.
rewrite sequence_end_app.
rewrite Hend_R0.
rewrite Hq_entry.
apply R1R0_output_mod6; assumption.
* exists ops.
split; [reflexivity|].
split.
--
subst ops ops2.
apply (valid_sequence_app m (repeat_R0 d) (repeat_R1R0 d1)).
++ exact Hseq_R0.
++ rewrite Hend_R0.
rewrite Hq_entry.
apply (proj1 (R1R0_entry_number_produces_repeat d1 n1 Hd1 Hn1)).
-- split.
++
subst m_final ops ops2.
rewrite sequence_end_app.
rewrite Hend_R0.
reflexivity.
++
subst ops ops2.
rewrite app_length.
rewrite repeat_R0_length.
rewrite repeat_R1R0_length.
assert (Hd1_le_log2q1 : d1 <= log2 q + 1).
{
assert (Hd1_le_log2q : d1 <= log2 (q + 1)).
{ apply (R1R0_entry_d_log2_bound q d1 n1); try assumption; lia. }
assert (Hlog2q1_le : log2 (q + 1) <= log2 q + 1).
{
assert (Hle : q + 1 <= 2 * q) by lia.
apply Nat.le_trans with (log2 (2 * q)).
- apply log2_monotone. exact Hle.
- rewrite log2_mult_power2; [lia | lia].
}
lia.
}
assert (Hlog2_m : log2 m = log2 q + d).
{
assert (Hm_qpow : m = q * 2 ^ d).
{ rewrite Hm_factor. ring. }
rewrite Hm_qpow.
rewrite log2_mul_pow2; [reflexivity | lia].
}
rewrite Hlog2_m.
assert (Hlen_le : d + 2 * d1 <= 2 * (log2 q + d + 1)).
{
apply Nat.le_trans with (d + 2 * (log2 q + 1)).
- apply Nat.add_le_mono_l.
apply Nat.mul_le_mono_pos_l; [lia|exact Hd1_le_log2q1].
- lia.
}
exact Hlen_le.
+
destruct Hq_case as [Hq_even _].
unfold is_even, is_odd in *.
rewrite Hq_odd in Hq_even.
discriminate.
Qed.

(* 迭代宏步展开的下界 *)
Theorem mod62_macrostep_iterated_lower_bound :
  forall t m0, t >= 1 -> m0 mod 6 = 2 ->
    exists mt chains, length chains = 2 * t /\
      valid_chains_condition chains /\
      mt mod 6 = 2 /\
      2 * t <= sum_contributions (extract_simple_chains chains) /\
      chains_R0_advantage chains.
Proof.
induction t as [|t IHt].
-
intros; lia.
-
intros m0 Ht Hmod.
destruct t.
+
apply mod62_R0advantage in Hmod.
destruct Hmod as [d0 [n0 [d1 [n1 [m1 [m2 [Hvalid [Hadv [Hmod2 Hsum]]]]]]]]].
exists m2, [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)].
split; [reflexivity|].
split; [exact Hvalid|].
split; [exact Hmod2|].
split.
*
assert (Hd0 : d0 >= 1).
{ destruct Hvalid as [_ Hforall].
specialize (Hforall (false, d0, n0, m0, m1)).
assert (Hin : In (false, d0, n0, m0, m1) [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)]).
{ left; auto. }
apply Hforall in Hin.
destruct Hin as [Hd0 _].
exact Hd0. }
rewrite Hsum. lia.
*
exact Hadv.
+
apply mod62_R0advantage in Hmod.
destruct Hmod as [d0 [n0 [d1 [n1 [m1 [m2 [Hvalid1 [Hadv1 [Hmod2 Hsum1]]]]]]]]].
assert (Ht' : S t >= 1) by lia.
apply IHt with (m0 := m2) in Ht'; auto.
destruct Ht' as [mt [chains_rest [Hlen_rest [Hvalid_rest [Hmod_rest [Hsum_rest Hadv_rest]]]]]].
exists mt, ([(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)] ++ chains_rest).
split. { simpl. rewrite Hlen_rest. lia. }
split. {
split. {
intro Hcontra.
apply app_eq_nil in Hcontra.
destruct Hcontra as [Hfirst Hrest].
simpl in Hfirst.
discriminate.
}
intros bdnds Hin.
apply in_app_or in Hin. destruct Hin.
-
destruct Hvalid1 as [_ Hforall1].
specialize (Hforall1 bdnds H).
exact Hforall1.
-
destruct Hvalid_rest as [_ Hforall_rest].
specialize (Hforall_rest bdnds H).
exact Hforall_rest.
}
split. { exact Hmod_rest. }
split. {
rewrite extract_simple_chains_app.
rewrite sum_contributions_app.
rewrite Hsum1.
assert (Hd0 : d0 >= 1).
{ destruct Hvalid1 as [_ Hforall1].
specialize (Hforall1 (false, d0, n0, m0, m1)).
assert (Hin : In (false, d0, n0, m0, m1) [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)]).
{ left; auto. }
apply Hforall1 in Hin.
destruct Hin as [Hd0 _].
exact Hd0. }
assert (Hsum_ge : sum_contributions (extract_simple_chains chains_rest) >= 2 * S t).
{ exact Hsum_rest. }
lia.
}
apply chains_R0_advantage_app; auto.
Qed.

(* a combination of the two previous theorems. *)
Theorem global_mod62_advantage_growth :
  forall m t,
    valid_input m ->
    t >= 1 ->
    exists (k : nat) (m2 mt : nat)
           (ops : list CollatzOp)
           (chains : list (bool * nat * nat * nat * nat)),
      (* conversion stage *)
      m2 mod 6 = 2 /\
      length ops = k /\
      valid_sequence ops m /\
      sequence_end m ops = m2 /\
      k <= 2 * (log2 m + 1) /\
      (* macrostep stage *)
      length chains = 2 * t /\
      valid_chains_condition chains /\
      mt mod 6 = 2 /\
      2 * t <= sum_contributions (extract_simple_chains chains) /\
      chains_R0_advantage chains.
Proof.
intros m t Hm Ht.
destruct (direct_conversion_to_mod6_2_orbit m Hm)
as [k [m2 [Hm2_mod6 [ops [Hlen_ops [Hvalid_ops [Hend_ops Hk_bound]]]]]]].
destruct (mod62_macrostep_iterated_lower_bound t m2 Ht Hm2_mod6)
as [mt [chains [Hlen_chains [Hchains_valid [Hmt_mod6 [Hsum_ge Hadv]]]]]].
exists k, m2, mt, ops, chains.
refine (conj Hm2_mod6 _).
refine (conj Hlen_ops _).
refine (conj Hvalid_ops _).
refine (conj Hend_ops _).
refine (conj Hk_bound _).
refine (conj Hlen_chains _).
refine (conj Hchains_valid _).
refine (conj Hmt_mod6 _).
refine (conj Hsum_ge Hadv).
Qed.

(* r0 优势随序列长度增长定理 *)
Theorem R0_advantage_growth :
  forall m t,
  valid_input m -> t >= 1 ->
  exists (r0_total r1_total : nat) (k : nat) (m2 mt : nat)
         (ops : list CollatzOp)
         (chains : list (bool * nat * nat * nat * nat)),
    (* 从global_mod6_orbit_advantage_growth获取chains *)
    m2 mod 6 = 2 /\
    length ops = k /\
    valid_sequence ops m /\
    sequence_end m ops = m2 /\
    k <= 2 * (log2 m + 1) /\
    length chains = 2 * t /\
    valid_chains_condition chains /\
    mt mod 6 = 2 /\
    2 * t <= sum_contributions (extract_simple_chains chains) /\
    chains_R0_advantage chains /\
    (* 定义总序列和操作计数 *)
    let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
    count_operations total_seq = (r0_total, r1_total) /\
    (* 比例保证 *)
    r0_total > r1_total /\
    r0_total - r1_total >= 2 * t.
Proof.
intros m t Hm Ht.
destruct (global_mod62_advantage_growth m t Hm Ht) as
(k & m2 & mt & ops & chains & Hm2_mod6 & Hlen_ops & Hvalid_ops & Hend_ops & Hk_bound & Hlen_chains & Hchains_valid & Hmt_mod6 & Hsum_ge & Hadv).
remember (concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains)) as total_seq eqn:Htotal_seq.
destruct (count_operations total_seq) as [r0_total r1_total] eqn:Hcounts.
exists r0_total, r1_total, k, m2, mt, ops, chains.
split; [exact Hm2_mod6|].
split; [exact Hlen_ops|].
split; [exact Hvalid_ops|].
split; [exact Hend_ops|].
split; [exact Hk_bound|].
split; [exact Hlen_chains|].
split; [exact Hchains_valid|].
split; [exact Hmt_mod6|].
split; [exact Hsum_ge|].
split; [exact Hadv|].
split.
- rewrite <- Htotal_seq.
rewrite Hcounts.
reflexivity.
-
unfold chains_R0_advantage in Hadv.
destruct Hadv as [Hgt Heq].
rewrite <- Htotal_seq in Hgt, Heq.
rewrite Hcounts in Hgt, Heq.
simpl in Hgt, Heq.
split.
+ exact Hgt.
+ rewrite Heq.
exact Hsum_ge.
Qed.

(* R0优势下界定理 *)
Theorem R0_advantage_lower_bound :
  forall m t,
  valid_input m -> t >= 1 ->
  exists (r0_total r1_total : nat) (k : nat) (m2 mt : nat)
         (ops : list CollatzOp)
         (chains : list (bool * nat * nat * nat * nat)),
    (* 保持原有条件 *)
    m2 mod 6 = 2 /\
    length ops = k /\
    valid_sequence ops m /\
    sequence_end m ops = m2 /\
    k <= 2 * (log2 m + 1) /\
    length chains = 2 * t /\
    valid_chains_condition chains /\
    mt mod 6 = 2 /\
    2 * t <= sum_contributions (extract_simple_chains chains) /\
    chains_R0_advantage chains /\
    let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
    count_operations total_seq = (r0_total, r1_total) /\
    (* 新的不等式形式 *)
    r0_total >= 2 * t + r1_total.
Proof.
intros m t Hm Ht.
destruct (R0_advantage_growth m t Hm Ht) as
(r0_total & r1_total & k & m2 & mt & ops & chains & Hcond).
exists r0_total, r1_total, k, m2, mt, ops, chains.
destruct Hcond as [Hm2_mod6 [Hlen_ops [Hvalid_ops [Hend_ops [Hk_bound [Hlen_chains [Hchains_valid [Hmt_mod6 [Hsum_ge [Hadv [Htotal_seq_def Hcount]]]]]]]]]]].
split; [exact Hm2_mod6|].
split; [exact Hlen_ops|].
split; [exact Hvalid_ops|].
split; [exact Hend_ops|].
split; [exact Hk_bound|].
split; [exact Hlen_chains|].
split; [exact Hchains_valid|].
split; [exact Hmt_mod6|].
split; [exact Hsum_ge|].
split; [exact Hadv|].
split; [exact Htotal_seq_def|].
destruct Hcount as [Hgt Hcount_diff].
change (r1_total < r0_total) in Hgt.
assert (Hr1_le_r0 : r1_total <= r0_total).
{ apply Nat.lt_le_incl. exact Hgt. }
assert (Hsum_plus : 2 * t + r1_total <= (r0_total - r1_total) + r1_total).
{ apply (Nat.add_le_mono_r (2 * t) (r0_total - r1_total) r1_total). exact Hcount_diff. }
assert (Hsub_add_le : (r0_total - r1_total) + r1_total <= r0_total).
{ rewrite Nat.sub_add; [apply Nat.le_refl| exact Hr1_le_r0]. }
eapply Nat.le_trans; [exact Hsum_plus| exact Hsub_add_le].
Qed.