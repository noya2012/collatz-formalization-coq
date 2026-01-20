Load "collatz_part_14.v".

(* Canonical pattern transformation theorem: odd numbers leading R1R0 sequence must be followed by R0 *)

Theorem odd_leads_R1R0_then_R0_pattern : forall m d n,
  m >= 1 -> d >= 1 -> n >= 0 -> m = valid_R1R0_entry_number d n ->
  exists Send,
    sequence_end m (repeat_R1R0 d) = Send /\
    is_even Send /\
    (2 * 3 ^ d * n <= Send /\ Send < 2 * 3 ^ d * (n + 1) /\ 3 ^ d - 1 <= Send) /\
    build_k_steps m (S d) = repeat_R1R0 d ++ [R0] /\
    (forall d' n', d' >= 1 -> n' >= 0 -> m = valid_R1R0_entry_number d' n' -> d' = d /\ n' = n).
Proof.
intros m d n Hm Hd Hn Hrepr.
pose proof (build_k_steps_numeric_canonical m Hm) as Hcanonical.
destruct Hcanonical as [[d0 [n0 [Hd0 [Hn0 [Hmdef [Hbuild [Hrange0 Hunique0]]]]]]] | [d0 [n0 [Hd0 [Hn0 [Hodd [Hmdef [Hbuild [Heq Hunique1]]]]]]]]].
-
pose proof (Hunique0 d n Hd Hn Hrepr) as Hunique_result.
destruct Hunique_result as [Hd_eq Hn_eq].
subst d0 n0.
set (Send := sequence_end m (repeat_R1R0 d)).
assert (HevenSend : Nat.even Send = true).
{
unfold Send.
rewrite Hmdef.
pose proof (repeat_R1R0_output_even d n Hd Hn) as [k Hk].
rewrite Hk.
apply even_2x.
}
destruct Hrange0 as [Hrange_low [Hrange_high Hrange_lower_bound]].
exists Send.
split; [reflexivity |].
split; [unfold is_even; exact HevenSend |].
split.
{ repeat split; assumption. }
split.
{ pose proof (build_k_steps_Sn m d Hm) as Hstep.
rewrite Hbuild in Hstep.
simpl in Hstep.
fold Send in Hstep.
unfold is_even in HevenSend.
rewrite HevenSend in Hstep.
simpl in Hstep.
exact Hstep. }
{ intros d' n' Hd' Hn' Hrepr'.
pose proof (Hunique0 d' n' Hd' Hn' Hrepr') as Hunique_result'.
destruct Hunique_result' as [Hd_eq' Hn_eq'].
split; assumption. }
-
exfalso.
pose proof (valid_R0R0_entry_number_properties d0 n0 Hd0 Hn0) as [_ Heven_m].
unfold is_even in Heven_m.
rewrite <- Hmdef in Heven_m.
pose proof (valid_R1R0_entry_number_odd d n Hd Hn) as Hodd_m.
unfold is_odd in Hodd_m.
rewrite <- Hrepr in Hodd_m.
rewrite Heven_m in Hodd_m.
discriminate.
Qed.

(* Canonical pattern transformation theorem: even numbers leading R0 sequence must be followed by R1R0 *)

Theorem even_leads_R0_then_R1R0_pattern : forall m d n,
  m >= 1 -> d >= 1 -> n >= 1 -> is_odd n -> m = valid_R0R0_entry_number d n ->
  exists Send,
    sequence_end m (repeat_R0 d) = Send /\
    is_odd Send /\
    Send = n /\
    build_k_steps m (S d) = repeat_R0 d ++ [R1; R0] /\
    (forall d' n', d' >= 1 -> n' >= 1 -> is_odd n' -> m = valid_R0R0_entry_number d' n' -> d' = d /\ n' = n).
Proof.
intros m d n Hm Hd Hn Hodd Hrepr.
pose proof (build_k_steps_numeric_canonical m Hm) as Hcanonical.
destruct Hcanonical as [[d0 [n0 [Hd0 [Hn0 [Hmdef [Hbuild [Hrange0 Hunique0]]]]]]] | [d0 [n0 [Hd0 [Hn0 [Hodd0 [Hmdef [Hbuild [Hseq Hunique1]]]]]]]]].
-
exfalso.
pose proof (valid_R1R0_entry_number_properties d0 n0 Hd0 Hn0) as [_ Hodd_m].
unfold is_odd in Hodd_m.
rewrite <- Hmdef in Hodd_m.
pose proof (valid_R0R0_entry_number_properties d n Hd Hn) as [_ Heven_m].
unfold is_even in Heven_m.
rewrite <- Hrepr in Heven_m.
rewrite Hodd_m in Heven_m.
discriminate.
-
pose proof (Hunique1 d n Hd Hn Hodd Hrepr) as Hunique_result.
destruct Hunique_result as [Hd_eq Hn_eq].
subst d0 n0.
set (Send := sequence_end m (repeat_R0 d)).
assert (Hsend_eq : Send = n).
{
unfold Send.
exact (eq_sym Hn_eq).
}
assert (HoddSend : is_odd Send).
{
unfold is_odd.
rewrite Hsend_eq.
exact Hodd.
}
exists Send.
split; [reflexivity |].
split; [exact HoddSend |].
split; [exact Hsend_eq |].
split.
{
pose proof (build_k_steps_Sn m d Hm) as Hstep.
rewrite Hbuild in Hstep.
simpl in Hstep.
fold Send in Hstep.
assert (HevenSend_false : Nat.even Send = false).
{ unfold is_odd in HoddSend. exact HoddSend. }
rewrite HevenSend_false in Hstep.
simpl in Hstep.
exact Hstep.
}
{
intros d' n' Hd' Hn' Hodd' Hrepr'.
pose proof (Hunique1 d' n' Hd' Hn' Hodd' Hrepr') as Hunique_result'.
destruct Hunique_result' as [Hd_eq' Hn_eq'].
split.
- exact Hd_eq'.
- rewrite <- Hsend_eq.
unfold Send.
exact Hn_eq'.
}
Qed.

(* Simplified entry predicates that directly include m >= 1 to avoid redundant derivation in subsequent proofs R1R0*)
Definition R1R0_entry (m d n : nat) : Prop := m >= 1 /\ d >= 1 /\ n >= 0 /\ m = valid_R1R0_entry_number d n.

(* Simplified entry predicates that directly include m >= 1 to avoid redundant derivation in subsequent proofs R0*)
Definition R0R0_entry (m d n : nat) : Prop := m >= 1 /\ d >= 1 /\ n >= 1 /\ is_odd n /\ m = valid_R0R0_entry_number d n.

(* R1R0 entry -> next entry (R0R0) construction *)
Lemma next_entry_from_R1R0 : forall m d n,
  R1R0_entry m d n ->
  exists Send d' n',
    sequence_end m (repeat_R1R0 d) = Send /\
    is_even Send /\
    R0R0_entry Send d' n' /\
    build_k_steps m (S d) = repeat_R1R0 d ++ [R0].
Proof.
intros m d n [Hm [Hd [Hn Hrepr]]].
pose proof (odd_leads_R1R0_then_R0_pattern m d n Hm Hd Hn Hrepr) as Hodd_cycle.
destruct Hodd_cycle as [Send [Hseq [Heven [Hbounds [Hnext _]]]]].
destruct Hbounds as [Hlower [Hupper Hmin]].
assert (Hthreepow_minus_ge1 : 3 ^ d - 1 >= 1).
{
assert (Hthreepow_minus_ge2 : 3 ^ d - 1 >= 2).
{ replace 2 with (3 ^ 1 - 1) by (simpl; reflexivity).
apply Nat.sub_le_mono_r.
apply Nat.pow_le_mono_r; lia. }
lia. }
assert (HSend_ge1 : Send >= 1).
{
apply (Nat.le_trans _ (3 ^ d - 1)); [exact Hthreepow_minus_ge1 | exact Hmin]. }
pose proof (build_k_steps_numeric_canonical Send HSend_ge1) as Hcanon.
destruct Hcanon as
[ [d0 [n0 [Hd0 [Hn0 [HSendDef [Hbuild0 [Hrange0 Huniq0]]]]]]] |
[d0 [n0 [Hd0 [Hn0 [Hodd0 [HSendDef [Hbuild0 [Hseq0 Huniq1]]]]]]]] ].
-
exfalso.
pose proof (valid_R1R0_entry_number_is_odd d0 n0 Hd0 Hn0) as HoddSend.
unfold is_odd in HoddSend.
rewrite <- HSendDef in HoddSend.
unfold is_even in Heven.
rewrite HoddSend in Heven; discriminate.
-
exists Send; exists d0; exists n0.
unfold R0R0_entry; repeat split; try assumption.
Qed.

(* R0R0 entry -> next entry (R1R0) construction *)
Lemma next_entry_from_R0R0 : forall m d n,
  R0R0_entry m d n ->
  exists Send d' n',
    sequence_end m (repeat_R0 d) = Send /\
    is_odd Send /\
    R1R0_entry Send d' n' /\
    build_k_steps m (S d) = repeat_R0 d ++ [R1; R0].
Proof.
intros m d n [Hm [Hd [Hn [Hodd Hrepr]]]].
pose proof (even_leads_R0_then_R1R0_pattern m d n Hm Hd Hn Hodd Hrepr) as Heven_cycle.
destruct Heven_cycle as [Send [Hseq [HoddSend [Hsend_eq [Hnext _]]]]].
assert (HSend_ge1 : Send >= 1) by (rewrite Hsend_eq; lia).
pose proof (build_k_steps_numeric_canonical Send HSend_ge1) as Hcanon.
destruct Hcanon as
[ [d0 [n0 [Hd0 [Hn0 [HSendDef [Hbuild0 [Hrange0 Huniq0]]]]]]] |
[d0 [n0 [Hd0 [Hn0 [Hodd0 [HSendDef [Hbuild0 [Hseq0 Huniq1]]]]]]]] ].
-
exists Send; exists d0; exists n0.
split; [ exact Hseq | ].
split; [ exact HoddSend | ].
split; [
unfold R1R0_entry; repeat split; try assumption
| exact Hnext ].
-
exfalso.
pose proof (valid_R0R0_entry_number_properties d0 n0 Hd0 Hn0) as [_ HevenSend].
unfold is_even in HevenSend.
rewrite <- HSendDef in HevenSend.
unfold is_odd in HoddSend.
rewrite HevenSend in HoddSend; discriminate.
Qed.
