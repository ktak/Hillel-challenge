Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Import ListNotations.

Definition leftpad {A:Type} (l:list A) pad len :=
  (repeat pad (len - length l)) ++ l.

Theorem leftpad_length :
  forall {A:Type} (l:list A) pad n,
    length (leftpad l pad n) = max (length l) n.
Proof.
unfold leftpad.
intros A l pad n.
rewrite app_length, repeat_length.
destruct (n <=? length l) eqn:H.
- apply Nat.leb_le in H.
  rewrite Nat.max_l; omega.
- apply Nat.leb_nle in H.
  rewrite Nat.max_r; omega.
Qed.

Lemma repeat_Forall :
  forall {A:Type} (x:A) n, Forall (fun y => y = x) (repeat x n).
Proof.
induction n; simpl; auto.
Qed.

Lemma firstn_prefix :
  forall {A:Type} (l1 l2:list A) n, n = length l1 ->
    firstn n (l1 ++ l2) = l1.
Proof.
induction l1; intros l2 n H; subst; simpl; auto.
rewrite IHl1; auto.
Qed.

Lemma skipn_suffix :
  forall {A:Type} (l1 l2:list A) n, n = length l1 ->
    skipn n (l1 ++ l2) = l2.
Proof.
induction l1; intros l2 n H; subst; simpl; auto.
Qed.

Theorem leftpad_pad :
  forall {A:Type} (l:list A) pad n,
    Forall (fun x => x = pad) (firstn (n - length l) (leftpad l pad n)) /\
    skipn (n - length l) (leftpad l pad n) = l.
Proof.
unfold leftpad.
intros A l pad n.
split.
- rewrite firstn_prefix.
  + apply repeat_Forall.
  + rewrite repeat_length; auto.
- rewrite skipn_suffix; auto.
  rewrite repeat_length; auto.
Qed.

Fixpoint unique (l:list nat) :=
match l with
| [] => []
| h::t => set_add PeanoNat.Nat.eq_dec h (unique t)
end.

Theorem unique_NoDup : forall l, NoDup (unique l).
Proof.
induction l; simpl.
- constructor.
- apply set_add_nodup. auto.
Qed.

Theorem unique_In_iff :
  forall l x, In x l <-> In x (unique l).
Proof.
induction l; simpl;
intros x; split; intros H;
try contradiction.
- apply set_add_iff.
  destruct H; auto.
  right. apply IHl. auto.
- apply set_add_iff in H.
  destruct H; auto.
  right. apply IHl. auto.
Qed.

Local Open Scope Z_scope.

Definition list_sum (l:list Z) := fold_left Z.add l 0.

Definition abs_diff x y := Z.abs (x - y).

Definition abs_diff_at_index (l:list Z) (index:nat) :=
  abs_diff (list_sum (firstn (S index) l)) (list_sum (skipn (S index) l)).

Fixpoint fulcrum_with_carries (l:list Z) (index:nat) prefix_sum :=
match l with
| [] => (index, abs_diff prefix_sum 0, 0)
| h::t =>
  let '(min_idx, min, suffix_sum) :=
    fulcrum_with_carries t (index+1) (prefix_sum+h)
  in
  if abs_diff (prefix_sum+h) suffix_sum <=? min
    then (index, abs_diff (prefix_sum+h) suffix_sum, suffix_sum+h)
    else (min_idx, min, suffix_sum+h)
end.

Definition fulcrum (l:list Z) := (fst (fst (fulcrum_with_carries l 0 0))).

Lemma fold_left_add :
  forall l x, fold_left Z.add l x = x + fold_left Z.add l 0.
Proof.
induction l; simpl; intros x; try omega.
rewrite (IHl (x+a)), (IHl a).
omega.
Qed.

Lemma list_sum_cons :
  forall h t, list_sum (h::t) = h + list_sum t.
Proof.
unfold list_sum.
intros h t; simpl.
rewrite fold_left_add.
auto.
Qed.

Lemma list_sum_app :
  forall l1 l2, list_sum (l1++l2) = list_sum l1 + list_sum l2.
Proof.
induction l1; simpl; intros l2; auto.
rewrite list_sum_cons, IHl1, list_sum_cons.
omega.
Qed.

Lemma skipn_all :
  forall {A:Type} n (l:list A), Nat.le (length l) n -> skipn n l = [].
Proof.
induction n; simpl; intros l H;
destruct l; auto.
- inversion H.
- apply IHn.
  simpl in H.
  apply Peano.le_S_n; auto.
Qed.

Lemma fulcrum_with_carries_suffix_sum :
  forall l i p, snd (fulcrum_with_carries l i p) = list_sum l.
Proof.
induction l; simpl;
intros i p; auto.
destruct (fulcrum_with_carries l (Nat.add i 1) (p+a)) as (x, s) eqn:Hrec.
destruct x as (idx, m).
rewrite list_sum_cons.
specialize (IHl (Nat.add i 1) (p+a)).
rewrite Hrec in IHl; simpl in IHl.
destruct (abs_diff (p+a) s <=? m); simpl;
omega.
Qed.

Lemma fulcrum_with_carries_fst_snd :
  forall suf pre,
    abs_diff_at_index
     (pre++suf)
     (fst (fst (fulcrum_with_carries suf (length pre) (list_sum pre)))) =
    snd (fst (fulcrum_with_carries suf (length pre) (list_sum pre))).
Proof.
induction suf; simpl; intros pre.
- rewrite <- app_nil_end. unfold abs_diff_at_index; simpl.
  destruct pre; auto.
  rewrite skipn_all, firstn_all2; simpl; try omega; auto.
- destruct (fulcrum_with_carries suf (length pre + 1) (list_sum pre + a))
    as (x, s) eqn:Hrec.
  destruct x as (idx, m).
  specialize (IHsuf (pre++[a])).
  rewrite list_sum_app in IHsuf.
  replace (list_sum [a]) with a in IHsuf by auto.
  rewrite app_length in IHsuf; simpl in IHsuf.
  destruct (abs_diff (list_sum pre + a) s <=? m); simpl;
  rewrite Hrec in IHsuf; simpl in IHsuf;
  replace (pre++a::suf) with (pre++[a]++suf) by auto;
  rewrite app_assoc;
  auto.
  unfold abs_diff_at_index.
  rewrite firstn_prefix;
    [| rewrite app_length; simpl; rewrite Nat.add_1_r; auto].
  rewrite list_sum_app, skipn_suffix;
    [| rewrite app_length; simpl; rewrite Nat.add_1_r; auto].
  rewrite <- (fulcrum_with_carries_suffix_sum
    suf (length pre + 1) (list_sum pre + a)).
  rewrite Hrec; simpl.
  auto.
Qed.

Lemma abs_diff_abs_diff_at_index :
  forall suf pre x,
    abs_diff (list_sum (pre++[x])) (list_sum suf) =
    abs_diff_at_index (pre++[x]++suf) (length pre).
Proof.
intros.
unfold abs_diff_at_index.
replace (S (length pre)) with (length (pre ++ [x]))
 by (rewrite app_length, Nat.add_1_r; auto).
rewrite app_assoc, firstn_prefix, skipn_suffix; auto.
Qed.

Lemma fulcrum_with_carries_le_abs_diff_at_ge_indexes :
  forall n pre suf,
    snd (fst (fulcrum_with_carries suf (length pre) (list_sum pre))) <=
    abs_diff_at_index (pre++suf) (length pre + n).
Proof.
induction n; simpl; intros pre suf.
- rewrite Nat.add_0_r.
  destruct suf; simpl.
  + unfold abs_diff_at_index, list_sum.
    rewrite <- app_nil_end, firstn_all2, skipn_all; simpl; auto; omega.
  + destruct (fulcrum_with_carries suf (length pre + 1) (list_sum pre + z))
      as (x, s) eqn:Hrec.
    destruct x as (idx, m).
    replace (pre++z::suf) with (pre++[z]++suf) by auto.
    rewrite <- abs_diff_abs_diff_at_index.
    rewrite <- (fulcrum_with_carries_suffix_sum
      suf (length pre + 1) (list_sum pre + z)).
    rewrite Hrec; simpl.
    destruct (abs_diff (list_sum pre + z) s <=? m) eqn:Hdiff; simpl;
    rewrite list_sum_app; unfold list_sum in *; simpl in *;
    try omega.
    apply Z.leb_gt in Hdiff.
    omega.
- destruct suf; simpl.
  + rewrite <- app_nil_end.
    unfold abs_diff_at_index.
    rewrite <- Nat.add_succ_r.
    rewrite firstn_all2, skipn_all; try apply Nat.le_add_r; try omega.
    unfold list_sum; simpl; omega.
  + destruct (fulcrum_with_carries suf (length pre + 1) (list_sum pre + z))
      as (x, s) eqn:Hrec.
    destruct x as (idx, m).
    specialize (IHn (pre++[z]) suf).
    rewrite list_sum_app, app_length in IHn; simpl in IHn.
    replace (list_sum [z]) with z in IHn by auto.
    rewrite Hrec, <- app_assoc, plus_assoc_reverse in IHn.
    destruct (abs_diff (list_sum pre + z) s <=? m) eqn:Hdiff; simpl;
    auto.
    apply Z.le_trans with m; auto.
    apply Z.leb_le in Hdiff; auto.
Qed.

Theorem fulcrum_correct :
  forall l n, Z.le (abs_diff_at_index l (fulcrum l)) (abs_diff_at_index l n).
Proof.
unfold fulcrum.
intros l n.
pose proof (fulcrum_with_carries_fst_snd l []) as H.
unfold list_sum in H; simpl in H.
rewrite H; clear H.
pose proof (fulcrum_with_carries_le_abs_diff_at_ge_indexes n [] l) as H.
unfold list_sum in H; simpl in H.
auto.
Qed.