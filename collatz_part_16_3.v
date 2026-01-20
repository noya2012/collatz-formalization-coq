Load "collatz_part_16_2.v".

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