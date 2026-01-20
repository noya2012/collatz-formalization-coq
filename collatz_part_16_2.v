Load "collatz_part_16.v".



(* Canonical chain definition R1R0-entry or R0R0-entry patterns *) 
Definition canonical_chain (entry_kind : bool) (d : nat) : list CollatzOp :=
  if entry_kind then repeat_R1R0 d ++ [R0] else repeat_R0 d ++ [R1; R0].

(* Sum contributions R1R0-entry adds 1 R0R0-entry adds d *)
Fixpoint sum_contributions (chains : list (bool * nat)) : nat :=
  match chains with
  | nil => 0
  | (b, d) :: rest =>
      let contribution := if b then 1 else d in
      contribution + sum_contributions rest
  end.

(*Convert chain list to operation sequence *)
Fixpoint chains_to_sequence (chains : list (bool * nat)) : list CollatzOp :=
  match chains with
  | nil => nil
  | (b, d) :: rest =>
      canonical_chain b d ++ chains_to_sequence rest
  end.

(* Length facts for the two patterns *)
Lemma length_repeat_R1R0 : forall d, length (repeat_R1R0 d) = 2 * d.
Proof.
induction d; simpl; auto. rewrite IHd. lia.
Qed.


(* Count R1 operations in repeat_R1R0 d ++ [R0] pattern *)
Lemma count_R1_repeat_R1R0_plus_R0 : forall d,
  d >= 0 ->
  snd (count_operations (repeat_R1R0 d ++ [R0])) = d.
Proof.
intros d Hd.
induction d as [|d' IH].
- simpl. reflexivity.
- simpl repeat_R1R0.
replace (repeat_R1R0 (S d') ++ [R0]) with (R1 :: R0 :: repeat_R1R0 d' ++ [R0]).
+ simpl count_operations.
remember (count_operations (repeat_R1R0 d' ++ [R0])) as counts eqn:Hcount.
destruct counts as [r0s r1s].
cbn [fst snd].
assert (Hd' : d' >= 0) by lia.
pose proof (IH Hd') as IH'.
cbn [fst snd] in IH'.
lia.
+ reflexivity.
Qed.

(* Helper lemma: Count R0 and R1 operations in repeat_R0 d ++ [R1; R0] *)
Lemma count_R0_repeat_R0_plus_R1R0 : forall d,
  d >= 0 ->
  fst (count_operations (repeat_R0 d ++ [R1; R0])) = d + 1.
Proof.
intros d Hd.
induction d as [|d' IH].
- simpl. reflexivity.
- simpl repeat_R0.
replace (repeat_R0 (S d') ++ [R1; R0]) with (R0 :: repeat_R0 d' ++ [R1; R0]).
+ simpl count_operations.
remember (count_operations (repeat_R0 d' ++ [R1; R0])) as counts eqn:Hcount.
destruct counts as [r0s r1s].
cbn [fst snd].
assert (Hd' : d' >= 0) by lia.
pose proof (IH Hd') as IH'.
cbn [fst snd] in IH'.
lia.
+ reflexivity.
Qed.

(* Helper lemma: Count R0 and R1 operations in repeat_R1R0 d ++ [R0] *)
Lemma count_R0_repeat_R1R0_plus_R0 : forall d,
  d >= 0 ->
  fst (count_operations (repeat_R1R0 d ++ [R0])) = d + 1.
Proof.
intros d Hd.
induction d as [|d' IH].
- simpl. reflexivity.
- simpl repeat_R1R0.
replace (repeat_R1R0 (S d') ++ [R0]) with (R1 :: R0 :: repeat_R1R0 d' ++ [R0]).
+ simpl count_operations.
remember (count_operations (repeat_R1R0 d' ++ [R0])) as counts eqn:Hcount.
destruct counts as [r0s r1s].
cbn [fst snd].
assert (Hd' : d' >= 0) by lia.
pose proof (IH Hd') as IH'.
cbn [fst snd] in IH'.
lia.
+ reflexivity.
Qed.

(* Helper lemma: Count R1 operations in repeat_R0 d ++ [R1; R0] *)
Lemma count_R1_repeat_R0_plus_R1R0 : forall d,
  d >= 0 ->
  snd (count_operations (repeat_R0 d ++ [R1; R0])) = 1.
Proof.
intros d Hd.
induction d as [|d' IH].
- simpl. reflexivity.
- simpl repeat_R0.
replace (repeat_R0 (S d') ++ [R1; R0]) with (R0 :: repeat_R0 d' ++ [R1; R0]).
+ simpl count_operations.
remember (count_operations (repeat_R0 d' ++ [R1; R0])) as counts eqn:Hcount.
destruct counts as [r0s r1s].
cbn [fst snd].
assert (Hd' : d' >= 0) by lia.
pose proof (IH Hd') as IH'.
cbn [fst snd] in IH'.
lia.
+ reflexivity.
Qed.

(* Exact counts for a canonical chain *)
Lemma count_operations_canonical_chain : forall b d,
  d >= 1 ->
  count_operations (canonical_chain b d) =
  (if b then (d + 1, d) else (d + 1, 1)).
Proof.
intros [] d Hd; unfold canonical_chain.
-
simpl.
rewrite (surjective_pairing (count_operations (repeat_R1R0 d ++ [R0]))).
rewrite count_R0_repeat_R1R0_plus_R0 by lia.
rewrite count_R1_repeat_R1R0_plus_R0 by lia.
reflexivity.
-
simpl.
rewrite (surjective_pairing (count_operations (repeat_R0 d ++ [R1; R0]))).
rewrite count_R0_repeat_R0_plus_R1R0 by lia.
rewrite count_R1_repeat_R0_plus_R1R0 by lia.
reflexivity.
Qed.


(* R0 advantage theorem: R0 operations always outnumber R1 operations *)
Theorem canonical_chain_R0_advantage : forall b d,
  d >= 1 ->
  let '(r0s, r1s) := count_operations (canonical_chain b d) in
  r0s > r1s /\ r0s - r1s = (if b then 1 else d).
Proof.
intros b d Hd.
destruct b.
- pose proof (count_operations_canonical_chain true d Hd) as Hc.
simpl in Hc. simpl. rewrite Hc. simpl. split; lia.
- pose proof (count_operations_canonical_chain false d Hd) as Hc.
simpl in Hc. simpl. rewrite Hc. simpl. split; lia.
Qed.



(* Count properties of repeat_R1R0 *)
Lemma count_repeat_R1R0 : forall d, count_operations (repeat_R1R0 d) = (d, d).
Proof.
intro d. induction d.
- simpl. reflexivity.
- simpl. rewrite IHd. simpl. reflexivity.
Qed.

(* Count properties of repeat_R0 *)
Lemma count_repeat_R0 : forall d, count_operations (repeat_R0 d) = (d, 0).
Proof.
intro d. induction d.
- simpl. reflexivity.
- simpl. rewrite IHd. simpl. reflexivity.
Qed.



(* Count operations for concatenated sequences: additive property *)
Lemma count_operations_app : forall (ops1 ops2 : list CollatzOp),
  count_operations (ops1 ++ ops2) =
    let '(r0s1, r1s1) := count_operations ops1 in
    let '(r0s2, r1s2) := count_operations ops2 in
    (r0s1 + r0s2, r1s1 + r1s2).
Proof.
induction ops1 as [|op ops1 IH]; intros ops2.
- simpl. destruct (count_operations ops2) as [r0s2 r1s2]; reflexivity.
- simpl.
specialize (IH ops2).
destruct (count_operations ops1) as [r0s1 r1s1] eqn:Hops1.
destruct (count_operations ops2) as [r0s2 r1s2] eqn:Hops2.
simpl in IH.
rewrite IH.
destruct op; simpl.
+ reflexivity.
+ reflexivity.
Qed.

(* Helper lemma: chain list count equals sum of individual chain counts *)
Lemma count_operations_chains_sequence : forall chains,
  fst (count_operations (chains_to_sequence chains)) =
  sum_contributions chains + snd (count_operations (chains_to_sequence chains)).
Proof.
intros chains.
induction chains as [| [b d] rest IH].
- simpl. reflexivity.
- simpl chains_to_sequence.
simpl count_operations.
destruct b.
+
destruct (count_operations (chains_to_sequence rest)) as [r0r r1r] eqn:Heq_r.
simpl.
unfold canonical_chain.
rewrite count_operations_app.
simpl.
rewrite count_operations_app.
simpl.
assert (Hd : d >= 0) by lia.
destruct (count_operations (repeat_R1R0 d)) as [r0s r1s] eqn:Hcounts.
rewrite count_repeat_R1R0 in Hcounts.
assert (Hr0s : r0s = d).
{ injection Hcounts as Hr0s_eq Hr1s_eq. symmetry. assumption. }
assert (Hr1s : r1s = d).
{ injection Hcounts as Hr0s_eq Hr1s_eq. symmetry. assumption. }
destruct (count_operations [R0]) as [r0_single r1_single] eqn:Hsingle.
simpl.
rewrite Heq_r.
simpl.
simpl in IH.
rewrite IH.
simpl.
rewrite Hr0s.
rewrite Hr1s.
lia.
+
destruct (count_operations (chains_to_sequence rest)) as [r0r r1r] eqn:Heq_r.
simpl.
unfold canonical_chain.
rewrite count_operations_app.
simpl.
rewrite count_operations_app.
simpl.
assert (Hd : d >= 0) by lia.
destruct (count_operations (repeat_R0 d)) as [r0s r1s] eqn:Hcounts.
rewrite count_repeat_R0 in Hcounts.
assert (Hr0s : r0s = d).
{ injection Hcounts as Hr0s_eq Hr1s_eq. symmetry. assumption. }
assert (Hr1s : r1s = 0).
{ injection Hcounts as Hr0s_eq Hr1s_eq. symmetry. assumption. }
destruct (count_operations [R1; R0]) as [r0_single r1_single] eqn:Hsingle.
simpl.
rewrite Heq_r.
simpl.
simpl in IH.
rewrite IH.
simpl.
rewrite Hr0s.
rewrite Hr1s.
lia.
Qed.

(* Generalized theorem: R0 advantage of concatenated canonical chains *)
Theorem generalized_concatenated_chains_R0_advantage :
  forall (chains : list (bool * nat)),
  chains <> nil ->
  (forall bd, In bd chains -> let (b, d) := bd in d >= 1) ->
  fst (count_operations (chains_to_sequence chains)) > snd (count_operations (chains_to_sequence chains)) /\
  fst (count_operations (chains_to_sequence chains)) - snd (count_operations (chains_to_sequence chains)) = sum_contributions chains.
Proof.
intros chains Hnonempty Hvalid.
pose proof (count_operations_chains_sequence chains) as Hcount.
destruct chains as [| [b d] rest] eqn:Hchains.
- contradiction.
- simpl.
destruct b.
+
assert (Hcontribution_pos : 1 + sum_contributions rest > 0) by lia.
simpl chains_to_sequence.
split.
*
rewrite count_operations_app.
destruct (count_operations (canonical_chain true d)) as [r0b r1b] eqn:Hcount_b.
destruct (count_operations (chains_to_sequence rest)) as [r0r r1r] eqn:Hcount_r.
simpl.
pose proof (count_operations_canonical_chain true d (Hvalid (true, d) (or_introl eq_refl))) as Hcanonical.
rewrite Hcanonical in Hcount_b.
injection Hcount_b as Hr0b Hr1b.
pose proof (count_operations_chains_sequence rest) as Hcount_rest.
rewrite Hcount_r in Hcount_rest.
simpl in Hcount_rest.
simpl.
rewrite <- Hr0b; rewrite <- Hr1b.
rewrite Hcount_rest.
lia.
*
rewrite count_operations_app.
destruct (count_operations (canonical_chain true d)) as [r0b r1b] eqn:Hcount_b.
destruct (count_operations (chains_to_sequence rest)) as [r0r r1r] eqn:Hcount_r.
simpl.
pose proof (count_operations_canonical_chain true d (Hvalid (true, d) (or_introl eq_refl))) as Hcanonical.
rewrite Hcanonical in Hcount_b.
injection Hcount_b as Hr0b Hr1b.
pose proof (count_operations_chains_sequence rest) as Hcount_rest.
rewrite Hcount_r in Hcount_rest.
simpl in Hcount_rest.
simpl.
rewrite <- Hr0b; rewrite <- Hr1b.
rewrite Hcount_rest.
lia.
+
assert (Hd_ge_1 : d >= 1).
{
specialize (Hvalid (false, d)).
assert (Hin : In (false, d) ((false, d) :: rest)) by (left; reflexivity).
apply Hvalid in Hin.
simpl in Hin.
exact Hin.
}
assert (Hcontribution_pos : d + sum_contributions rest > 0) by lia.
simpl chains_to_sequence.
split.
*
rewrite count_operations_app.
destruct (count_operations (canonical_chain false d)) as [r0b r1b] eqn:Hcount_b.
destruct (count_operations (chains_to_sequence rest)) as [r0r r1r] eqn:Hcount_r.
simpl.
pose proof (count_operations_canonical_chain false d Hd_ge_1) as Hcanonical.
rewrite Hcanonical in Hcount_b.
injection Hcount_b as Hr0b Hr1b.
pose proof (count_operations_chains_sequence rest) as Hcount_rest.
rewrite Hcount_r in Hcount_rest.
simpl in Hcount_rest.
simpl.
rewrite <- Hr0b; rewrite <- Hr1b.
rewrite Hcount_rest.
lia.
*
rewrite count_operations_app.
destruct (count_operations (canonical_chain false d)) as [r0b r1b] eqn:Hcount_b.
destruct (count_operations (chains_to_sequence rest)) as [r0r r1r] eqn:Hcount_r.
simpl.
pose proof (count_operations_canonical_chain false d Hd_ge_1) as Hcanonical.
rewrite Hcanonical in Hcount_b.
injection Hcount_b as Hr0b Hr1b.
pose proof (count_operations_chains_sequence rest) as Hcount_rest.
rewrite Hcount_r in Hcount_rest.
simpl in Hcount_rest.
simpl.
rewrite <- Hr0b; rewrite <- Hr1b.
rewrite Hcount_rest.
lia.
Qed.


(* Extract simple chains from full chain information: keep only (b,d) pairs *)
Definition extract_simple_chains (chains : list (bool * nat * nat * nat * nat)) : list (bool * nat) :=
  map (fun '(b, d, _, _, _) => (b, d)) chains.

(* Non-empty chains: simple chains non-empty iff original chains non-empty *)
Lemma extract_simple_chains_nonempty : forall chains,
  chains <> nil <-> extract_simple_chains chains <> nil.
Proof.
intros chains.
split.
- intros Hnonempty.
destruct chains as [|hd tl]; [contradiction|].
unfold extract_simple_chains.
simpl. discriminate.
- intros Hnonempty.
destruct chains as [|hd tl]; [contradiction|].
discriminate.
Qed.

(* Valid chains: d >= 1 preserved in simple chain extraction *)
Lemma extract_simple_chains_valid : forall chains,
  (forall bdnds, In bdnds chains ->
    let '(b, d, n, m, Send) := bdnds in d >= 1) ->
  forall bd, In bd (extract_simple_chains chains) ->
    let (b, d) := bd in d >= 1.
Proof.
intros chains Hvalid bd Hin.
unfold extract_simple_chains in Hin.
apply in_map_iff in Hin.
destruct Hin as [x [Heq Hin_orig]].
destruct x as [[[[b' d'] n'] m'] Send'].
destruct bd as [b'' d''].
injection Heq as <- <-.
specialize (Hvalid (b', d', n', m', Send') Hin_orig).
exact Hvalid.
Qed.

(* Canonical chains to sequence: equivalence between two representations *)
Lemma canonical_chains_to_sequence : forall chains,
  concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) =
  chains_to_sequence (extract_simple_chains chains).
Proof.
intros chains.
unfold extract_simple_chains.
induction chains as [| x rest IH].
- reflexivity.
- destruct x as [[[[b d] n] m] Send].
simpl.
rewrite <- IH.
reflexivity.
Qed.

(* Generalized R0 advantage theorem: valid chain sequences maintain R0 advantage *)
Theorem generalized_valid_chains_sequence_R0_advantage :
  forall (chains : list (bool * nat * nat * nat * nat)),
  chains <> nil ->
  (forall bdnds, In bdnds chains ->
    let '(b, d, n, m, Send) := bdnds in
    d >= 1 /\
    ((b = true /\ n >= 0 /\ m = valid_R1R0_entry_number d n) \/
     (b = false /\ n >= 1 /\ is_odd n /\ m = valid_R0R0_entry_number d n)) /\
    ((b = true /\
      sequence_end m (repeat_R1R0 d) = Send /\ is_even Send) \/
     (b = false /\
      sequence_end m (repeat_R0 d) = Send /\ is_odd Send))) ->
  (let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
   fst (count_operations total_seq) > snd (count_operations total_seq) /\
   fst (count_operations total_seq) - snd (count_operations total_seq) =
   sum_contributions (extract_simple_chains chains)).
Proof.
intros chains Hnonempty Hvalid.
set (simple_chains := extract_simple_chains chains).
assert (Hsimple_nonempty : simple_chains <> nil).
{
apply extract_simple_chains_nonempty.
exact Hnonempty.
}
assert (Hsimple_valid : forall bd, In bd simple_chains -> let (b, d) := bd in d >= 1).
{
apply extract_simple_chains_valid.
intros bdnds Hin.
specialize (Hvalid bdnds Hin).
destruct bdnds as [[[[b d] n] m] Send].
destruct Hvalid as [Hd _].
exact Hd.
}
assert (Hgen :
fst (count_operations (chains_to_sequence simple_chains)) >
snd (count_operations (chains_to_sequence simple_chains)) /\
fst (count_operations (chains_to_sequence simple_chains)) -
snd (count_operations (chains_to_sequence simple_chains)) =
sum_contributions simple_chains).
{
apply generalized_concatenated_chains_R0_advantage;
[exact Hsimple_nonempty | exact Hsimple_valid].
}
assert (Heq_seq :
concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) =
chains_to_sequence simple_chains).
{
unfold simple_chains.
apply canonical_chains_to_sequence.
}
rewrite Heq_seq.
exact Hgen.
Qed.



(* Valid chain sequence condition: defines valid R1R0-entry or R0R0-entry chains *)
Definition valid_chain_sequence_condition (b : bool) (d : nat) (n : nat) (m : nat) (Send : nat) : Prop :=
  d >= 1 /\
  ((b = true /\ n >= 0 /\ m = valid_R1R0_entry_number d n /\
    sequence_end m (repeat_R1R0 d) = Send /\ is_even Send) \/
   (b = false /\ n >= 1 /\ is_odd n /\ m = valid_R0R0_entry_number d n /\
    sequence_end m (repeat_R0 d) = Send /\ is_odd Send)).

(* Corollary: R0 advantage for valid chain sequences using condition definition *)
Corollary valid_chains_sequence_R0_advantage_corollary :
  forall (chains : list (bool * nat * nat * nat * nat)),
  chains <> nil ->
  (forall bdnds, In bdnds chains ->
    let '(b, d, n, m, Send) := bdnds in
    valid_chain_sequence_condition b d n m Send) ->
  (let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
   let simple_chains := extract_simple_chains chains in
   fst (count_operations total_seq) > snd (count_operations total_seq) /\
   fst (count_operations total_seq) - snd (count_operations total_seq) =
   sum_contributions simple_chains).
Proof.
intros chains Hnonempty Hvalid.
assert (Hvalid' : forall bdnds, In bdnds chains ->
let '(b, d, n, m, Send) := bdnds in
d >= 1 /\
((b = true /\ n >= 0 /\ m = valid_R1R0_entry_number d n) \/
(b = false /\ n >= 1 /\ is_odd n /\ m = valid_R0R0_entry_number d n)) /\
((b = true /\
sequence_end m (repeat_R1R0 d) = Send /\ is_even Send) \/
(b = false /\
sequence_end m (repeat_R0 d) = Send /\ is_odd Send))).
{
intros bdnds Hin.
specialize (Hvalid bdnds Hin).
unfold valid_chain_sequence_condition in Hvalid.
destruct bdnds as [[[[b d] n] m] Send].
destruct Hvalid as [Hd Hcond].
split; [exact Hd|].
destruct Hcond as [[Hb_true [Hn [Hmdef [Hseq_end Heven]]]] |
[Hb_false [Hn [Hodd_n [Hmdef [Hseq_end Hodd]]]]]].
- subst b.
split.
+ left. tauto.
+ left. tauto.
- subst b.
split.
+ right. tauto.
+ right. tauto.
}
apply (generalized_valid_chains_sequence_R0_advantage chains Hnonempty Hvalid').
Qed.
