Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qminmax.
Require Import Coq.QArith.QOrderedType.
Require Import Lia. (*tactic: lia*)
Require Import Lqa. (*tactic: lra*)

Ltac destruct_guard_in H :=
    generalize H; clear H;
    lazymatch goal with
    | |- context [match ?X with _ => _ end] => 
        let e := fresh "E" in destruct X eqn: e; 
            let h := fresh H in intros h
    | |- context [if ?X then _ else _] => 
        let e := fresh "E" in destruct X eqn: e; 
            let h := fresh H in intros h
    end.

Ltac destruct_guard :=
    match goal with
    | |- context [match ?X with _ => _ end] => 
        let e := fresh "E" in destruct X eqn: e
    | |- context [if ?X then _ else _] => 
        let e := fresh "E" in destruct X eqn: e
    end.


Module Type T.
    Parameter V: Type.
    Parameter eqb: V -> V -> bool.
    Parameter equal: forall x y, reflect (x=y) (eqb x y).
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End T.

Module Type MapSpec (T:T).
    Import T.
    (* Map structure with default value stored in type *)
    Parameter t: forall (e:Type) {default:e}, Type.
    Parameter empty: forall {e:Type} (default:e), @t e default.
    Parameter replace: forall {e:Type} {d}, V -> e -> @t e d -> @t e d.
    Parameter find: forall {e:Type} {d}, @t e d -> V -> e.
    Parameter update: forall {e:Type} {d}, V -> (e->e) -> @t e d -> @t e d. 
    Notation "m [ v ]" := (find m v) (at level 12). 
End MapSpec.

Module Map (T:T) <: MapSpec (T).
    Import T.
    Definition t (e:Type) {default: e} := list (V * e).
    
    Definition empty {e:Type} d: @t e d := nil.

    Fixpoint remove {e:Type} {d} (v:V) (xs: @t e d) : @t e d :=
        match xs with 
        | nil => nil
        | ((u,y)::xs) => 
            if eqb v u then 
                @remove e d v xs 
            else 
                (u,y)::(@remove e d v xs)
        end.

    Fixpoint replace {e:Type} {d} (v:V) (x:e) (xs:@t e d) := 
        match xs with
        | nil => (v,x)::nil
        | ((u,y)::xs) => 
            if eqb v u then 
                (u,x)::(@remove e d v xs) 
            else 
                (u,y)::(@replace e d v x xs)
        end.

    Fixpoint update {e:Type} {d} (v:V) (f:e->e) (xs:@t e d) := 
        match xs with
        | nil => (v,f d)::nil
        | ((u,y)::xs) => 
            if eqb v u then 
                (u,f y)::(@remove e d v xs) 
            else 
                (u,y)::(@update e d v f xs)
        end.
    
    Fixpoint find {e:Type} {d} (xs:@t e d) (v:V) := 
        match xs with
        | nil => d
        | ((u,y)::xs) => 
            if eqb v u then 
                y
            else 
                @find e d xs v
        end.

    Lemma FindRemoveEq {e d} {f:e->e} (xs:@t e d) u  :  
        @find e d (remove u xs) u = d.
    Proof.
        intros. induction xs.
        + simpl. reflexivity.
        + simpl. destruct a.
        - destruct (equal u v).
        * auto.
        * simpl. rewrite -> eqb_neq; auto.
        Qed.

    Lemma FindRemoveNeq {e d} (xs:@t e d) u v  : u<>v -> 
        @find e d (remove v xs) u = @find e d xs u .
    Proof.
        intros. induction xs; auto.
        simpl. destruct a. destruct (equal v v0).
        + destruct (equal u v0).
        - subst. contradiction.
        - auto.
        + simpl. rewrite -> IHxs. reflexivity.
        Qed. 

    Lemma FindUpdateEq {e d} {f:e->e} (xs:@t e d) u  :
        @find e d (update u f xs) u = f (@find e d xs u) .
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u u); auto.
        - contradiction.
        + simpl. destruct a. destruct (equal u v).
        - simpl. subst v. destruct (equal u u); auto.
        * rewrite -> FindRemoveNeq; auto.
        -- contradiction.
        - simpl. destruct (equal u v).
        * subst. contradiction.
        * rewrite -> IHxs. reflexivity.
        Qed.

    Lemma FindUpdateNeq {e d} {f:e->e} (xs:@t e d) u v  : u<>v -> 
        @find e d (update v f xs) u = @find e d xs u .
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u v); auto.
        - contradiction.
        + simpl. destruct a. destruct (equal v v0).
        - simpl. subst. destruct (equal u v0).
        * contradiction.
        * rewrite -> FindRemoveNeq; auto.
        -  simpl. destruct (equal u v0); auto.
        Qed.
    
    Lemma FindReplaceEq {e d} {f:e} (xs:@t e d) u  :
        @find e d (replace u f xs) u = f .
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u u); auto.
        - contradiction.
        + simpl. destruct a. destruct (equal u v).
        - simpl. destruct (equal u v); auto.
        * contradiction.
        - simpl. destruct (equal u v).
        * contradiction.
        * rewrite -> IHxs. reflexivity.
        Qed.

    Lemma FindReplaceNeq {e d} {f:e} (xs:@t e d) u v  : u<>v -> 
        @find e d (replace v f xs) u = @find e d xs u .
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u v); auto.
        - contradiction.
        + simpl. destruct a. destruct (equal v v0).
        - simpl. subst. rewrite -> eqb_neq; auto.
        * rewrite -> FindRemoveNeq; auto. 
        - simpl. destruct (equal u v0); auto.
        Qed.
        
End Map.

Module Type SetSpec (T:T).
    Import T.
    Parameter t: Type.
    Parameter empty: t.
    Parameter add: V -> t -> t.
    Parameter mem: V -> t -> bool.
    Parameter choice: forall (s:t), option (V * t).
    Parameter filter: forall (p:V->bool), t -> t.
    (* Parameter fold_left: forall {a:Type}, (a -> V -> a) -> t -> a -> a. *)
    Notation "v ∈ s" := (mem v s) (at level 12). 
End SetSpec.

Module MkSet (T:T) <: SetSpec (T).
    Import T.
    Definition t := list V.
    Definition empty: t := nil.
    Fixpoint remove v s :=
        match s with 
        | nil => nil
        | v' :: s => if T.eqb v v' then remove v s else v' :: remove v s
        end.
    Definition add v s := v :: remove v s.
    Fixpoint mem v s :=
        match s with 
        | nil => false
        | v' :: s => if T.eqb v v' then true else mem v s
        end.

    Notation "v ∈ s" := (mem v s) (at level 12). 
    Definition choice s: option (V*t) := 
        match s with 
        | nil => None
        | v :: s => Some (v,s)
        end.
    Fixpoint filter (p:V->bool) (xs:t) := 
        match xs with
        | nil => nil
        | v::s => if p v then v::filter p s else filter p s 
        end.
    
    Lemma in_filter v (p:V->bool) s : (v ∈ (filter p s)) = true -> (v ∈ s)  = true  /\ p v = true.
    Proof.
        intros. split.
        + induction s; auto.
         simpl in *. destruct (equal v a); auto.
        - apply IHs. destruct (p a).
        * simpl in *. rewrite eqb_neq in H; auto.
        * auto.
        + induction s.
        - simpl in *. inversion H. 
        - simpl in H. destruct (p a) eqn : e.
        * simpl in *. destruct (equal v a); subst; auto.
        * auto.  
        Qed.

    Lemma filter_in v (p:V->bool) s : (v ∈ s)  = true -> p v = true -> (v ∈ (filter p s)) = true.
    Proof.
        intros. induction s; auto.
        simpl in *. destruct (p a).
        + simpl. destruct (equal v a); auto.
        + apply IHs. destruct (equal v a); auto.
        - subst. admit. (*???*)
    Admitted.

    Definition fold_left {a:Type} (f:a -> V -> a) (xs:t) (x:a) := 
        fold_left f xs x.
End MkSet.


Module Tuple (T U:T) <: T.
    Definition V := (T.V * U.V)%type.
    Definition eqb '(a,b) '(c,d) := T.eqb a c && U.eqb b d.
    Definition equal (x y:V): reflect (x=y) (eqb x y).
    Proof. 
        destruct x, y. simpl. 
        destruct (T.equal v v1), (U.equal v0 v2); subst; 
            simpl; constructor; intuition; inversion H; auto.
    Qed.
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Tuple.

Module PR (T:T).
    Import T.
    Definition R := Q.

    Module Edge := Tuple (T) (T).

    Declare Scope EMap.
    Module EMap := Map (Edge).
    Notation "m '[' v ']'" := (EMap.find m v) (at level 12):EMap. 
    Open Scope EMap.

    Module VSet := MkSet (T).
    Notation "v '∈v' s" := (VSet.mem v s) (at level 12). 

    Module ESet := MkSet (Edge).
    Notation "v '∈e' s" := (ESet.mem v s) (at level 12). 

    Definition Graph := (VSet.t * ESet.t)%type.
    Definition FlowNet := (Graph * (V -> V -> R) * V * V)%type.

    Definition QLe (a b: Q): bool :=
        match Qlt_le_dec b a with
        | left _ => false
        | right _ => true
        end.
    Infix "<=?" := QLe : Q_scope.
    Definition QLt (a b: Q): bool :=
        match Qlt_le_dec a b with
        | left _ => true
        | right _ => false
        end.
    Infix "<?" := QLt : Q_scope.
    Definition QInfLt (x y: option Q): bool :=
        match x, y with
        | Some a, Some b => a <? b
        | Some _, None => true
        | _, _ => false
        end.

    Lemma QLt_spec x y: reflect (x<y)%Q (x<?y)%Q.
    Proof.
        unfold QLt. destruct_guard; constructor; lra.
    Qed.

    Definition QSumList :=
        fold_right Qplus 0 .
        
    Definition excess (fn:FlowNet) (f: @EMap.t R 0) : V -> R :=
        let '((vs, es),c,s,t) := fn in
        fun u => 
            QSumList (map (fun v => f[(v,u)]) vs) -
            QSumList (map (fun v => f[(u,v)]) vs) .
    
    Definition res_cap (fn: FlowNet) (f: @EMap.t R 0) u v : R :=
        let '((vs, es),c,s,t) := fn in
        if (u,v) ∈e es then
            c u v -  f[(u,v)]
        else 
            f[(v,u)] 
    .

    Definition E (fn: FlowNet) (f: @EMap.t R 0)  :=
        let '((vs, es),c,s,t) := fn in
        ESet.filter (fun '(u, v) => f[(u,v)] <? c u v) es.    
    
    Definition res_net (fn: FlowNet) (f: @EMap.t R 0)  : FlowNet :=
        let '((vs, es),c,s,t) := fn in
        ((vs,E fn f),res_cap fn f,s,t).

    Module NMap := Map (T).
    Declare Scope NMap.
    Notation "m '[' v ']'" := (NMap.find m v) (at level 12):NMap. 
    
    
    (* Notation "t $ r" := (t r) (at level 65, right associativity, only parsing). *)

    Definition push fn f u v : @EMap.t R 0 :=
        let '((vs, es),c,s,t) := fn in
        let delta := Qmin (excess fn f u) (res_cap fn f u v) in
        if (u,v) ∈e es  then
             (EMap.update (u,v) (fun x=>x+delta) f)
        else 
            (EMap.update (v,u) (fun x=>x-delta) f)
    .
    
    Definition option_min (x:option nat) (y:nat): option nat :=
        match x with
        | None => Some y
        | Some a => Some (min a y)
        end.

    Local Open Scope NMap.
    Definition relabel_find fn f (l:@NMap.t nat O) u vs := 
        let fvs := VSet.filter (fun v => 0 <? res_cap fn f u v) vs in
        VSet.fold_left (fun r v => 
            match r with 
            | None => Some v 
            | Some r => if (l[r] <=? l[v])%nat then Some r else Some v 
            end) fvs None 
        .  
    
    Definition relabel fn f (l:@NMap.t nat O) u : option (@NMap.t nat O):=
        let '((vs, es),c,s,t) := fn in
        match relabel_find fn f l u vs with
        | None => None
        | Some n => Some (NMap.replace u (1+l[n])%nat l)
        end.

    Fixpoint find_push_node fn f (l:@NMap.t nat O) u vs' :=
        let '((vs, es),c,s,t) := fn in
        match vs' with
        | nil => None
        | v::vs' => 
            if (l[u]=? 1+l[v])%nat &&
                (0 <? res_cap fn f u v) 
            then
                Some v
            else 
                find_push_node fn f l u vs'
        end.


    Definition has_excess_not_sink fn f v  :=
        let '((vs, es),c,s,t) := fn in
        if T.eqb v t then
            false
        else if 0 <? excess fn f v then 
            true
        else
            false
    .

    Inductive Tr : Type :=
        | Init {d}: @EMap.t Q d -> @NMap.t nat O -> VSet.t ->  Tr
        | Push {d}: V -> V -> @EMap.t Q d -> VSet.t ->  Tr
        | Relabel : V -> nat -> @NMap.t nat O ->  Tr
        | OutOfGas
        | RelabelFailed
        .

    Fixpoint gpr_helper_trace fn f l ac g tr : (@EMap.t Q 0*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        match g with
        | O => (f, OutOfGas::tr)
        | S g' => 
            match VSet.choice ac with
            | None => (f,tr)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let f' := push fn f u v in
                let ac' := if 0 <? (excess fn f' u) then ac else ac' in
                if has_excess_not_sink fn f' v  then 
                    let ac'' := VSet.add v ac' in
                    gpr_helper_trace fn f' l ac'' g' (Push u v f' ac''::tr)
                else 
                    gpr_helper_trace fn f' l ac' g' (Push u v f' ac'::tr)
            | None =>
                match relabel fn f l u with
                | None => (f, RelabelFailed::tr)
                | Some l' =>
                    gpr_helper_trace fn f l' ac g' (Relabel u (l'[u]) l'::tr)
                end
            end
            end 
        end.

    Local Close Scope NMap.
    Fixpoint initial_push fn f ac es: (@EMap.t Q 0*list V)  :=
        let '((_, _),c,s,t) := fn in
        match es with
        | nil => (f,ac)
        | (u,v)::es => 
            if T.eqb s u then 
                let f' := EMap.replace (u,v) (c u v) f in
                let ac := 
                    if has_excess_not_sink fn f' v then 
                        (VSet.add v ac) 
                    else 
                        ac 
                in
                initial_push fn f' ac es  
            else
                initial_push fn f ac es
        end.

    Import Coq.Arith.PeanoNat.


    Local Open Scope NMap.
    Definition gpr_trace (fn:FlowNet) : (@EMap.t Q 0*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        let labels := NMap.replace s (length vs) (NMap.empty O) in
        let bound := (length es * length vs * length vs)%nat in
        let '(f, active) := initial_push fn (EMap.empty 0) nil es in
        gpr_helper_trace fn f labels active bound (Init f labels active :: nil).

    Local Close Scope NMap.
    Definition CapacityConstraint (fn:FlowNet) (f:@EMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, ESet.mem (u,v) es = true -> 
            f[(u,v)] <= c u v.
    
    Definition NonDeficientFlowConstraint (fn:FlowNet) (f:@EMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v <> s -> 0 <= excess fn f v.

    Definition FlowConservationConstraint (fn:FlowNet) (f:@EMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> v<>t -> excess fn f v = 0.
    
    Definition PreFlowCond (fn:FlowNet) (f:@EMap.t Q 0) := 
            CapacityConstraint fn f /\ NonDeficientFlowConstraint fn f. 
    
    Definition ActiveNode (fn:FlowNet) (f:@EMap.t Q 0)v := 
        let '((vs, es),c,s,t) := fn in
        (v ∈v vs) = true -> excess fn f v > 0.
    
    Local Open Scope NMap.
    Definition ValidLabeling  fn (f:@EMap.t Q 0) (l:@NMap.t nat O) :=
        forall u v,
        let '((vs, es),c,s,t) := fn in
        ((u,v) ∈e E fn f) = true  ->  (l[u] <= l[v] + 1)%nat.

    Inductive CPath (fn:FlowNet) (f:@EMap.t Q 0): V -> V -> Prop :=
    | Start u : CPath fn f u u
    | Step u v1 vn: ((u,v1) ∈e E fn f) = true -> CPath fn f v1 vn ->  CPath fn f u vn
    .

    Definition NoAugPath (fn:FlowNet) (f:@EMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        CPath fn f s t -> False.
    
    Definition PushCondition fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u v := 
        excess fn f u > 0 /\ (l[u] = l[v] + 1)%nat.
    
    Lemma PushValidLabel fn (f:@EMap.t Q 0) (l:@NMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        ValidLabeling fn f l -> PushCondition fn f l x y
                -> ValidLabeling fn (push fn f x y) l.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, PushCondition.
        intros. unfold push in H1. destruct ((x, y) ∈e es) eqn : E.
        + unfold PR.E in *. apply ESet.in_filter in H1. destruct H1.  
        apply H. apply ESet.filter_in.
        - auto.
        - destruct (Edge.equal (x,y) (u, v)).
        * inversion e. subst. rewrite EMap.FindUpdateEq in H2. 
        eapply (reflect_iff _ _ (QLt_spec _ _)). 
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2.
        unfold res_cap in H2. rewrite E in H2.
        destruct ( Q.min_dec (excess (vs, es, c, s, t) f u) (c u v - EMap.find f (u, v))).
        ** rewrite q in H2. lra.
        ** rewrite q in H2. unfold R in H2. lra.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        + unfold PR.E in *. apply ESet.in_filter in H1. destruct H1.
        destruct (Edge.equal (y, x) (u, v)).
        - inversion e. subst. lia.
        - rewrite EMap.FindUpdateNeq in H2; auto.
        apply H. apply ESet.filter_in; auto.
        Qed.

    Definition RelabelCondition fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u := 
      excess fn f u > 0 /\ forall v, res_cap fn f u v > 0 -> (l[u] <= l[v])%nat.


    Lemma minProp: forall a b, (min a b = a /\ a <= b)%nat \/ 
                                (min a b = b /\ b <= a)%nat.
    Proof. lia. Qed. 


    Lemma RFindResCapCondition fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u vs : forall vs' v,
        (VSet.filter (fun v0 : V => 0 <? res_cap fn f u v0) vs) = vs' ->
        (v ∈v vs') = true ->  (0 <? res_cap fn f u v) = true .
    Proof.
        induction vs; intros.
        + simpl in H. subst. simpl in H0. inversion H0.
        + simpl in H. destruct_guard_in H.
        - destruct (vs').
        * simpl in H0. inversion H0. 
        * inversion H. simpl in H0. destruct (equal v v0).
        ** subst. apply E0.
        ** subst. eapply IHvs; auto.
        - eapply IHvs.
        * apply H.
        * apply H0.
        Qed. 

    
    Lemma RFindMinSomeCondition (l:@NMap.t nat O) vs': forall v r vs'', 
    (r ∈v vs'') = true ->
    (forall v', (v' ∈v vs'') = true -> (l[r] <= l[v'])%nat) ->
        VSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' (Some r) = Some v ->
        forall v', ((v' ∈v vs') = true\/(v' ∈v vs'') = true) -> (l[v] <= l[v'])%nat.
    Proof. 
        induction vs'; intros.
        + simpl in H1. inversion H1. subst. apply H0. destruct H2; auto.
        simpl in H2. inversion H2.
        + simpl in H1. destruct (l [r] <=? l [a])%nat eqn : E.
        - simpl in H2. destruct H2. 
        * destruct (equal v' a); auto.
        ** subst. assert (l[v] <= l[r])%nat. { eapply IHvs' in H1; eauto. }
        apply Nat.leb_le in E. lia.
        ** eapply IHvs' in H1; eauto.
        * assert (l[v] <= l[r])%nat. { eapply IHvs' in H1; eauto. }
        specialize (H0 v' H2). lia.
        - simpl in H2. destruct H2. 
        * destruct (equal v' a); auto.
        ** subst. assert (a ∈v (a :: vs'') = true). {simpl. rewrite eqb_refl; auto. } 
        eapply IHvs' in H1; eauto.
        intros. simpl in H4. destruct (equal v' a). subst; auto. specialize (H0 v' H4).
        apply Nat.leb_gt in E. lia.  
        **  admit.
        * admit.
    Admitted.

    Lemma RFindMinNoneCondition (l:@NMap.t nat O) vs': forall v, 
        VSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
        forall v', ((v' ∈v vs') = true) -> (l[v] <= l[v'])%nat.
    Proof.
    Admitted.

    Lemma RFindMinMemCondition (l:@NMap.t nat O) vs': forall v, 
        VSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
            (v ∈v vs') = true.
    Proof.
    Admitted.
        

    Lemma RFindCondition fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u vs: forall v, 
      relabel_find fn f l u vs = Some v  ->
      (0 <? res_cap fn f u v) = true /\ (forall v', (v' ∈v vs) = true -> (0 <? res_cap fn f u v') = true -> (l[v] <= l[v'])%nat).
    Proof.
    Admitted.

    Lemma RFindMemCondition fn f (l:@NMap.t nat O) u vs: forall v, 
        relabel_find fn f l u vs = Some v ->
            (v ∈v vs) = true.
    Proof.
    Admitted.


    Lemma RelabelValidLabel fn (f:@EMap.t Q 0) (l:@NMap.t nat O) x l':
        let '((vs, es),c,s,t) := fn in
        ValidLabeling fn f l -> RelabelCondition fn f l x 
            -> relabel fn f l x = Some l' -> ValidLabeling fn f l'.
    Proof.
    Admitted.

End PR.

Module Nat <: T.
    Definition V := nat.
    Definition eqb := Nat.eqb.
    Lemma equal: forall x y, reflect (x=y) (eqb x y).
    Proof.
        induction x; destruct y; cbn; try constructor; auto.
        destruct (IHx y); subst; constructor; auto.
    Qed.
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Nat.

Module PRNat := PR (Nat).


Import ListNotations.
Open Scope nat.
Definition FN1 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 10%Q in
    (([0;1],[(0,1)]),c,0,1).

Compute (PRNat.gpr_trace FN1).

Definition FN2 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 
        match x, y with
        | 0, 1 => 15%Q
        | 0, 3 => 4%Q
        | 1, 2 => 12%Q
        | 2, 3 => 3%Q
        | 2, 5 => 7%Q
        | 3, 4 => 10%Q
        | 4, 1 => 5%Q
        | 4, 5 => 10%Q
        | _, _ => 0%Q
        end
    in
    (([0;1;2;3;4;5],[(0,1);(0,3);(1,2);(2,3);(2,5);(3,4);(4,1);(4,5)]),c,0,5).

Compute (PRNat.gpr_trace FN2).

Compute (@PRNat.excess FN2 [(0, 1, 10%Q); (0, 3, 4%Q); (3, 4, 7%Q); (
    4, 1, 0%Q); (1, 2, 10%Q); (2, 5, 7%Q); (
    4, 5, 7%Q); (2, 3, 3%Q)] 5).

