Require Import List Wellfounded.

Section Acc_incomp.

  Variables (X : Type) (R T : X -> X -> Prop) (P : X -> Prop).

  Hypothesis (H1 : forall x y, T x y -> P y -> R x y)
             (H2 : forall x y, T x y -> P y -> P x).

  Fact Acc_incomp x : Acc R x -> P x -> Acc T x.
  Proof. induction 1; constructor; eauto. Qed.

End Acc_incomp.

Section wf_finite.

  Variables (X : Type) (HX : exists l, forall x : X, In x l)
            (R : X -> X -> Prop).

  Infix "<" := R.

  Hypothesis X_irrefl : forall x, ~ x < x.
  Hypothesis X_trans : forall x y z, x < y -> y < z -> x < z.

  Local Definition restr l x y := In x l /\ x < y.

  Local Lemma wf_restr l : well_founded (restr l).
  Proof.
    induction l as [ | x l IHl ].
    + constructor; intros y ([] & _).
    + (* every point below x is Acc for restr (x::l) *)
      assert (Acc_lt_x : forall y, y < x -> Acc (restr (x::l)) y).
      1: { intros y H.
           specialize (IHl y); revert y IHl H.
           apply Acc_incomp.
           * intros a ? ([] & ?) G; subst.
             - destruct (X_irrefl a); eauto.
             - red; auto.
           * intros ? ? ([] & ?); subst; eauto. }
      (* so x is Acc for restr (x::l) *)
      assert (Acc_x : Acc (restr (x::l)) x).
      1: { constructor; intros ? []; auto. }
      (* so every point is Acc for restr (x::l) *)
      intros y.
      specialize (IHl y); revert y IHl.
      induction 1 as [ y _ IHy ].
      constructor; intros z ([] & ?); subst; auto.
      apply IHy; red; auto.
  Qed.

  Theorem wf_finite : well_founded R.
  Proof.
    destruct HX as (l & Hl).
    generalize (wf_restr l).
    apply wf_incl.
    split; auto.
  Qed.

End wf_finite.

Check wf_finite.