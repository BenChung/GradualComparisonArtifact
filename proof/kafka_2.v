Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapList.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrdersEx.
Module Nat_Pair_OT := PairOrderedType(Nat_as_OT)(Nat_as_OT).
Module PairNatList := MSetList.Make(Nat_Pair_OT).

(* Kafka definitions *)

Definition id := nat.
Definition this:id := 0.
Definition that:id := 0.
Definition ref := nat.
(* Cell = id [class] * [list of fields]  *)
Inductive Cell :=
| HCell : id * list ref -> Cell.
(* pointer to an object *)
Definition heap := list Cell.

Inductive type :=
| class : id -> type
| Any : type.
Definition env := list type.

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
  ForallT_nil : ForallT P nil
| ForallT_cons : forall (x : A) (l : list A), P x -> ForallT P l -> ForallT P (x :: l).
Arguments ForallT_nil {_ _}.
Arguments ForallT_cons {_ _ _ _}.

Unset Elimination Schemes.

Inductive expr :=
| Var : id -> expr
| Ref : ref -> expr (* location of object *)
| GetF : expr -> id -> expr
| SetF : expr -> id -> expr -> expr
| Call : expr -> id -> type -> type -> expr -> expr
| DynCall : expr -> id -> expr -> expr
| SubCast : type -> expr -> expr (* <t> *)
| BehCast : type -> expr -> expr (* << t >>*)
| New : id -> list expr -> expr.

Definition expr_rect (P : expr -> Type) (f : forall i : id, P (Var i)) (f0 : forall r : ref, P (Ref r))
           (f1 : forall e : expr, P e -> forall i : id, P (GetF e i))
           (f2 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (SetF e i e0))
           (f3 : forall e : expr, P e -> forall (i : id) (t t0 : type) (e0 : expr), P e0 -> P (Call e i t t0 e0))
           (f4 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (DynCall e i e0))
           (f5 : forall (t : type) (e : expr), P e -> P (SubCast t e))
           (f6 : forall (t : type) (e : expr), P e -> P (BehCast t e))
           (f7 : forall (i : id) (l : list expr), ForallT P l -> P (New i l)) :=
  fix F (e : expr) : P e :=
    match e as e0 return (P e0) with
    | Var i => f i
    | Ref r => f0 r
    | GetF e0 i => f1 e0 (F e0) i
    | SetF e0 i e1 => f2 e0 (F e0) i e1 (F e1)
    | Call e0 i t t0 e1 => f3 e0 (F e0) i t t0 e1 (F e1)
    | DynCall e0 i e1 => f4 e0 (F e0) i e1 (F e1)
    | SubCast t e0 => f5 t e0 (F e0)
    | BehCast t e0 => f6 t e0 (F e0)
    | New i l => f7 i l ((fix F' (l:list expr) : ForallT P l :=
                       match l with
                       | e :: r => ForallT_cons (F e) (F' r)
                       | nil => ForallT_nil 
                       end) l)
    end.

Definition expr_ind : forall (P : expr -> Prop) (f : forall i : id, P (Var i)) (f0 : forall r : ref, P (Ref r))
           (f1 : forall e : expr, P e -> forall i : id, P (GetF e i))
           (f2 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (SetF e i e0))
           (f3 : forall e : expr, P e -> forall (i : id) (t t0 : type) (e0 : expr), P e0 -> P (Call e i t t0 e0))
           (f4 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (DynCall e i e0))
           (f5 : forall (t : type) (e : expr), P e -> P (SubCast t e))
           (f6 : forall (t : type) (e : expr), P e -> P (BehCast t e))
           (f7 : forall (i : id) (l : list expr), ForallT P l -> P (New i l)), forall e : expr, P e := expr_rect.

Definition expr_rec : forall (P : expr -> Set) (f : forall i : id, P (Var i)) (f0 : forall r : ref, P (Ref r))
           (f1 : forall e : expr, P e -> forall i : id, P (GetF e i))
           (f2 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (SetF e i e0))
           (f3 : forall e : expr, P e -> forall (i : id) (t t0 : type) (e0 : expr), P e0 -> P (Call e i t t0 e0))
           (f4 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (DynCall e i e0))
           (f5 : forall (t : type) (e : expr), P e -> P (SubCast t e))
           (f6 : forall (t : type) (e : expr), P e -> P (BehCast t e))
           (f7 : forall (i : id) (l : list expr), ForallT P l -> P (New i l)), forall e : expr, P e := expr_rect.

Set Elimination Schemes.

Inductive fd :=
| Field : type -> fd.
Inductive md := (* m t t e *)
| Method : id -> type -> type -> expr -> md.
Inductive k :=
| ClassDef : list fd -> list md -> k.
Definition ct := list k.

(* well-formedness *)
Inductive WfType : type -> ct -> Prop :=
| WfClassType : forall c (k : ct), c < length k -> WfType(class c) k
| WfAny : forall k, WfType(Any) k.

Definition wf_type(t:type)(k:ct):{WfType t k} + {exists c, t = class c /\ length k <= c}.
Proof.
  destruct t.
  - destruct (le_lt_dec (length k) i).
    + right. exists i. split; auto.
    + left. apply WfClassType; auto.
  - left. apply WfAny.
Qed.

(* preliminary definition of class well-formedness, used for subtyping *)
Definition WfTClass(cd:k)(c:ct) := forall fds mds, cd = ClassDef fds mds ->
                                                  (forall m t1 t2 e, In (Method m t1 t2 e) mds ->
                                                                   WfType t1 c /\ WfType t2 c) /\
                                                  (forall t, In (Field t) fds -> WfType t c).

(* preliminary definition of class table well-formedness, used for subtyping *)
Definition WfTCt(c:ct) := forall k, In k c -> WfTClass k c.


(* Subtyping *)
Inductive Subtype : PairNatList.t -> ct -> type -> type -> Prop :=
| STRefl : forall m k t, Subtype m k t t
| STSeen : forall m k t1 t2, PairNatList.In (t1, t2) m ->
                             Subtype m k (class t1) (class t2)
| STClass : forall m m' k c d, m' = PairNatList.add (c,d) m ->
                               forall fds mds, nth_error k c = Some(ClassDef fds mds) ->
                               forall fds' mds', nth_error k d = Some(ClassDef fds' mds') ->
                               Md_Subtypes m' k mds mds' ->
                               Subtype m k (class c) (class d)
with Md_Subtypes : PairNatList.t -> ct -> list md -> list md -> Prop :=
     | MDCons : forall md1 md2 mu k r mds,
         (In md1 mds) ->
         (Md_Subtype mu k md1 md2)-> (Md_Subtypes mu k mds r) -> 
         (Md_Subtypes mu k mds (md2::r))
     | MDNil : forall mu k mds, (Md_Subtypes mu k mds nil)
with Md_Subtype : PairNatList.t -> ct -> md -> md -> Prop :=
     | MDSub : forall m mu k t1 t1' t2 t2' e e', (Subtype mu k t1 t1') -> (Subtype mu k t2' t2) ->
                                               Md_Subtype mu k (Method m t1' t2' e') (Method m t1 t2 e).

Scheme subtyping_ind := Induction for Subtype Sort Prop
                        with md_subtypings_ind := Induction for Md_Subtypes Sort Prop
                                                  with md_subtype_ind := Induction for Md_Subtype Sort Prop.

Definition empty_mu := PairNatList.empty.


Program Fixpoint compute_subtype (m : PairNatList.t)(k : ct)(kwf:WfTCt k)
        (a b : type)(awf:WfType k a)(bwf:WfType k b)
        {measure (PairNatList.cardinal (PairNatList.diff (equivalent_set (type_pair_universe k)) m))}
  : {Subtype m k a b} + {~ (Subtype m k a b)} :=
  match a, b with
  | Any, Any => _
  | (class C), (class D) =>
    match (Nat.eqb C D) with
    | true => _
    | false =>
      match PairNatList.mem (C,D) m with
        true => _
      | false =>
        let mu' := PairNatList.add (C,D) m in
        let mc := (methods C k) in
        let mD := (methods D k) in
        _
      end
    end
  | Any, (class C) => _
  | (class C), Any => _
  end.
Next Obligation.
  left. eauto.
Qed.
Next Obligation.
  left. symmetry in Heq_anonymous. rewrite Nat.eqb_eq in Heq_anonymous. subst. auto.
Qed.
Next Obligation.
  left. symmetry in Heq_anonymous. apply MProps.Dec.F.mem_2 in Heq_anonymous. apply STSeen. eauto.
Qed.
Next Obligation.
  remember (methods C k0) as mc.
  remember (methods D k0) as mD.
  remember (PairNatList.add (C,D) m) as mu'.
  destruct (compute_md_subtypes k0 mu' mc mD ((this, (class C))::nil) ((this, (class D))::nil) nil).
  - subst. apply methods_are_wf; eauto. 
  - subst. apply methods_are_wf; eauto.
  - refine (fun (a b:type)(wfa:WellFormedType k0 a)(wfb:WellFormedType k0 b) =>
              compute_subtype mu' k0 kwf a b wfa wfb _).
    eapply MProps.subset_cardinal_lt.
    + MDec.fsetdec.
    + assert (Hin: PairNatList.In (C,D) (PairNatList.diff (equivalent_set (type_pair_universe k0)) m)).
      {
        subst. apply MProps.FM.diff_3.
        - rewrite<- equiv_set_corr. apply tpu_correct; eauto. symmetry in Heq_anonymous0.
          rewrite Nat.eqb_neq in Heq_anonymous0. eauto.
        - symmetry in Heq_anonymous. rewrite<- MProps.Dec.F.not_mem_iff in Heq_anonymous. eauto. 
      } apply Hin.
    + rewrite PairNatList.diff_spec. unfold not. intros. inject H. apply H1.
      rewrite PairNatList.add_spec. left. auto.
  - left. subst. eapply STClass; eauto.
  - right. contradict n. inject n.
    + symmetry in Heq_anonymous0. rewrite Nat.eqb_neq in Heq_anonymous0. tauto.
    + symmetry in Heq_anonymous. rewrite<- MProps.Dec.F.not_mem_iff in Heq_anonymous. tauto.
    + apply H4.
Qed.
Next Obligation.
  right. intros H. inject H.
Qed.
Next Obligation.
  right. intros H. inject H.
Qed.
