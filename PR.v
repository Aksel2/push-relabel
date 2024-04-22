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

Ltac inv_clear H := inversion H; subst; clear H.

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

    Lemma MemAddEq (xs:t) v  :
        v ∈ (add v xs) = true.
    Proof.
        intros. simpl. destruct (equal v v); auto.
        Qed.

    Lemma MemRemoveEq (xs:t) u : 
        u ∈ (remove u xs) = false.
    Proof.
        intros. induction xs; auto.
        simpl. destruct (equal u a); auto.
        simpl. destruct (equal u a); auto.
        contradiction.
        Qed.

    Lemma MemRemoveNeq (xs:t) u v  : u<>v -> 
        u ∈ (remove v xs) = u ∈ xs.
    Proof.
        intros. induction xs; auto.
        simpl. destruct (equal v a).
        + subst. destruct (equal u a); auto.
        + destruct (equal u a).
        - subst. simpl. rewrite eqb_refl; auto.
        - simpl. destruct (equal u a); auto.
        subst. contradiction.
        Qed.

    Lemma MemAddNeq (xs:t) u v  : u<>v -> 
        u ∈ (add v xs) = u ∈ xs.
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u v); auto.
        contradiction.
        + simpl. destruct (equal u v).
        - destruct (equal u a); auto.
        subst. contradiction.
        - destruct (equal v a).
        * destruct (equal u a).
        ** subst. contradiction.
        ** subst. rewrite <- IHxs. inversion IHxs. destruct (equal u a).
        *** subst. contradiction.
        *** rewrite IHxs. apply H1.
        * destruct (equal u a).
        ** subst. simpl.  rewrite eqb_refl; auto.
        ** simpl. destruct (equal u a).
        *** subst. contradiction.
        *** simpl in *. destruct (equal u v); auto.
        subst. contradiction. 
        Qed.
        

    Definition choice s: option (V*t) := 
        match s with 
        | nil => None
        | v :: s => Some (v,s)
        end.

    Lemma choiceNone s: choice s = None <-> s=empty.
    Proof.
        intros. induction s.
        + split; auto.
        + split.
        - destruct IHs. simpl in *.
        intros. inversion H1.
        - intros. inversion H.
        Qed.

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
        simpl in *. destruct (p a) eqn : E.
        + simpl. destruct (equal v a); auto.
        + destruct (equal v a); auto.
        subst. apply IHs. rewrite <- H0. destruct (p a).
        - inversion E.
        - inversion H0.
        Qed.

    Definition fold_left {a:Type} (f:a -> V -> a) (xs:t) (x:a) := 
        fold_left f xs x.

    Inductive IsSet : t -> Prop :=
        | NilIsSet: IsSet nil
        | ConsIsSet {a xs} : (a ∈ xs) = false -> IsSet xs -> IsSet (a::xs).
    
    Lemma EmptyIsSet: IsSet empty.
    Proof.
        apply NilIsSet.
    Qed.


    Lemma RemoveOtherInFalse a b xs: a ∈ xs = false -> a ∈ remove b xs = false.
    Proof.
        intros. induction xs; auto.
        simpl. destruct (equal b a0).
        + apply IHxs. subst. inversion H. destruct (equal a a0); auto.
        inversion H1.
        + simpl. destruct (equal a a0).
        - subst. simpl in *. rewrite eqb_refl in H. inversion H.
        - apply IHxs. simpl in *. destruct (equal a a0); auto.
        subst. inversion H.
    Qed. 
    
    Lemma RemoveSameInFalse a xs: a ∈ remove a xs = false.
    Proof.
        intros. induction xs; auto.
        simpl. destruct (equal a a0); auto.
        simpl. destruct (equal a a0); auto.
        subst. contradiction.
        Qed.   

    Lemma RemoveIsSet a xs: IsSet xs -> IsSet (remove a xs).
    Proof.
        intros. induction xs; auto.
        simpl. destruct (equal a a0). 
        + subst. apply IHxs. inversion H. subst. apply H3.
        + inversion H. subst. apply ConsIsSet. 
        - rewrite <- H2. apply MemRemoveNeq.
        intro C. inv_clear C. contradiction.
        - auto.
         Qed.

    Lemma AddIsSet a xs: IsSet xs -> IsSet (add a xs).
    Proof. 
        intros. induction xs. 
        + unfold add. simpl. apply ConsIsSet; auto.
        + unfold add. simpl. destruct (equal a a0).
        - subst. inversion H. subst. auto.
        - inversion H. subst. apply ConsIsSet.
        * simpl. rewrite eqb_neq; auto.
        apply RemoveSameInFalse.
        * apply ConsIsSet.
        ** apply RemoveOtherInFalse. apply H2.
        ** apply RemoveIsSet. apply H3.
        Qed.

    Lemma ChoiceIsSet a xs: IsSet xs -> forall xs', choice xs = Some (a, xs') -> IsSet xs'.
    Proof.
        intros. induction xs.
        + inversion H0.
        + inversion H. subst. inversion H0. subst. apply H4.
    Qed.

    Lemma FilterOtherInFalse a f xs: a ∈ xs = false -> a ∈ filter f xs = false.
    Proof. 
        intros. induction xs; auto.
        simpl. destruct (f a0) eqn : E.
        + simpl. destruct (equal a a0).
        - subst. simpl in *. rewrite eqb_refl in H. inversion H.
        - apply IHxs. simpl in *. destruct (equal a a0); auto.
        subst. inversion H.
        + apply IHxs. simpl in *. destruct (equal a a0); auto.
        subst. inversion H.
        Qed.

    Lemma filterIsSet f xs: IsSet xs -> IsSet (filter f xs).
    Proof.
        intros. induction xs; auto.
        simpl. destruct (f a). 
        + apply ConsIsSet.
        - apply FilterOtherInFalse. inversion H. auto.
        - inversion H. subst. apply IHxs. apply H3.
        + inversion H. subst. apply IHxs. apply H3.
        Qed.

    Lemma choiceSome s: forall a s', 
    IsSet s ->
    choice s = Some (a,s') -> a ∈ s=true /\ s'=remove a s /\ IsSet s'.
    Proof.
        induction s; intros. 
        + inversion H0.
        + split.
        - simpl. destruct (equal a0 a). 
        * subst. auto.
        * inversion H. subst. simpl in H0. inversion H0. 
        subst. contradiction.
        - split.
        * simpl. destruct (equal a a0). 
        ** subst. rewrite eqb_refl. simpl in *. 
        inversion H. inversion H0. subst. clear -H3.
        induction s'; auto.  simpl in *. destruct (equal a0 a).
        *** inversion H3.
        *** rewrite <- IHs'; auto.
        ** rewrite eqb_neq; auto. simpl in *. inversion H0. contradiction.
        * simpl in *. inversion H0. inversion H. subst. auto.
        Qed.
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

    Definition nodes (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in vs.

    Definition sink (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in t.        
    
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

    Lemma QLt_false x y: (x <? y)%Q = false <-> y<=x .
    Proof. unfold QLt. destruct (Qlt_le_dec x y); split; intros.
    all: auto.
    all: try inversion H. lra.
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

    Fixpoint gpr_helper_trace fn f l ac g tr : (option (@EMap.t Q 0)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        match g with
        | O => (None, OutOfGas::tr)
        | S g' => 
            match VSet.choice ac with
            | None => (Some f,tr)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let f' := push fn f u v in
                let ac' := if 0 <? (excess fn f' u) then ac else ac' in
                if has_excess_not_sink fn f' v  then 
                    let ac'' := VSet.add v ac' in
                    gpr_helper_trace fn f' l ac'' g' (Push u v f' ac''::tr)
                else 
                    let ac'' := VSet.remove v ac' in
                    gpr_helper_trace fn f' l ac'' g' (Push u v f' ac'::tr)
            | None =>
                match relabel fn f l u with
                | None => (None, RelabelFailed::tr)
                | Some l' =>
                    gpr_helper_trace fn f l' ac g' (Relabel u (l'[u]) l'::tr)
                end
            end
            end 
        end.
    
    Lemma gpr_helper_trace_fn fn f l ac g tr : 
        gpr_helper_trace fn f l ac g tr =
            let '((vs, es),c,s,t) := fn in
            match g with
            | O => (None, OutOfGas::tr)
            | S g' => 
                match VSet.choice ac with
                | None => (Some f,tr)
                | Some (u,ac') =>
                match find_push_node fn f l u vs with
                | Some v =>
                    let f' := push fn f u v in
                    let ac' := if 0 <? (excess fn f' u) then ac else ac' in
                    if has_excess_not_sink fn f' v  then 
                        let ac'' := VSet.add v ac' in
                        gpr_helper_trace fn f' l ac'' g' (Push u v f' ac''::tr)
                    else 
                        let ac'' := VSet.remove v ac' in
                        gpr_helper_trace fn f' l ac'' g' (Push u v f' ac'::tr)
                | None =>
                    match relabel fn f l u with
                    | None => (None, RelabelFailed::tr)
                    | Some l' =>
                        gpr_helper_trace fn f l' ac g' (Relabel u (l'[u]) l'::tr)
                    end
                end
                end 
            end.
    Proof. destruct g; auto. Qed.

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
    Definition gpr_trace (fn:FlowNet) : (option (@EMap.t Q 0)*list Tr) :=
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
        forall v, (v ∈v vs) = true -> v<>s -> 0 <= excess fn f v.

    Definition FlowConservationConstraint (fn:FlowNet) (f:@EMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> v<>t -> excess fn f v == 0.
    
    Definition PreFlowCond (fn:FlowNet) (f:@EMap.t Q 0) := 
            CapacityConstraint fn f /\ NonDeficientFlowConstraint fn f. 

    Definition FlowMapPositiveConstraint (fn:FlowNet) (f:@EMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, f[(u,v)] >= 0 /\ c u v >= 0.
            
    Definition ActiveNode (fn:FlowNet) (f:@EMap.t Q 0)v := 
        let '((vs, es),c,s,t) := fn in
        (v ∈v vs) = true /\ excess fn f v > 0.
    
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

    Definition NoSteepArc (fn:FlowNet) (f:@EMap.t Q 0) (l:@NMap.t nat O):=
        forall u v,
        res_cap fn f u v > 0 -> (l[u] <= l[v]+1)%nat.

    Definition ResCapNodes (fn:FlowNet) (f:@EMap.t Q 0) :=
            forall u v,
            res_cap fn f u v > 0 -> u ∈v (nodes fn) = true /\ v ∈v (nodes fn) = true.

    Definition NoPushCondition fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u := 
                forall v, v ∈v (nodes fn) = true -> (l[u] <> l[v] + 1)%nat.
        
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
      excess fn f u > 0 /\ forall v, v ∈v (nodes fn) = true -> res_cap fn f u v > 0 -> (l[u] <= l[v])%nat.


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
        ** eapply IHvs' in H1.
        *** apply H1.
        *** instantiate (1 := a::vs''). simpl. rewrite eqb_refl. reflexivity.
        *** intros. simpl in H3.  destruct (equal v'0 a).
        **** subst. lia. 
        **** apply H0 in H3. apply Nat.leb_gt in E. lia. 
        *** left. apply H2.
        * eapply IHvs' in H1.
        ** apply H1.
        ** instantiate (1 := a::vs''). simpl. rewrite eqb_refl. reflexivity.
        ** intros. simpl in H3.  destruct (equal v'0 a).
        *** subst. lia. 
        *** apply H0 in H3. apply Nat.leb_gt in E. lia. 
        ** right. simpl. destruct (equal v' a); auto.
    Qed.

    Lemma RFindMinNoneCondition (l:@NMap.t nat O) vs': forall v, 
        VSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
        forall v', ((v' ∈v vs') = true) -> (l[v] <= l[v'])%nat.
    Proof.
        intros. induction vs'.
        + simpl in H0. inversion H0.
        + simpl in H. eapply (RFindMinSomeCondition _ _ _ a (a::nil)) in H.
        - apply H.
        - simpl. rewrite eqb_refl. reflexivity.
        - intros. simpl in H1. destruct (equal v'0 a); subst. auto.
        inversion H1.
        - simpl in H0. destruct (equal v' a).
        * subst. right. simpl. rewrite eqb_refl. reflexivity.
        * left. apply H0.
        Qed.

    Lemma RFindMinMemCondition (l:@NMap.t nat O) vs': forall v, 
        VSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
            (v ∈v vs') = true.
    Proof.
        intros. destruct vs'.
        + simpl in H. inversion H.
        + simpl in H. simpl. destruct (equal v v0); auto.
        generalize dependent v0. induction vs'; intros.
        - simpl in H. inversion H. destruct n. auto.
        - simpl in H. destruct ((l [v0] <=? l [a])%nat) eqn : E.
        * apply IHvs' in H; auto.  simpl. destruct (equal v a); auto.
        * simpl. destruct (equal v a); auto. apply IHvs' in H.
        ** simpl. destruct (equal v a); auto.
        ** auto.
        Qed. 


    Lemma RFindCondition fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u vs: forall v, 
      relabel_find fn f l u vs = Some v  ->
      (0 <? res_cap fn f u v) = true /\ (forall v', (v' ∈v vs) = true 
        -> (0 <? res_cap fn f u v') = true -> (l[v] <= l[v'])%nat).
    Proof.
        intros. unfold relabel_find in H. split.
        + apply RFindMinMemCondition in H. eapply VSet.in_filter in H. destruct H; auto.
        + intros. eapply RFindMinNoneCondition in H; eauto.
        apply VSet.filter_in; auto.
        Qed.

    Lemma RFindMemCondition fn f (l:@NMap.t nat O) u vs: forall v, 
        relabel_find fn f l u vs = Some v ->
            (v ∈v vs) = true.
    Proof.
        intros. unfold relabel_find in H. destruct vs.
        + simpl in H. inversion H.
        + simpl. destruct (equal v v0); auto.
        - apply RFindMinMemCondition in H. eapply VSet.in_filter in H. destruct H; auto.
        simpl in H. destruct (equal v v0); auto.
        Qed.


    Lemma RelabelValidLabel fn (f:@EMap.t Q 0) (l:@NMap.t nat O) x l':
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        ValidLabeling fn f l -> RelabelCondition fn f l x 
            -> relabel fn f l x = Some l' -> ValidLabeling fn f l'.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, RelabelCondition.
        intros R. intros. unfold relabel in H1. destruct_guard_in H1; [| inversion H1].
        inversion H1. clear H1 H4. apply H in H2 as P. unfold PR.E in H2. 
        apply ESet.in_filter in H2. destruct H2. destruct H0. 
        apply RFindMemCondition in E0 as P1. apply RFindCondition in E0.
        destruct E0. eapply (reflect_iff _ _ (QLt_spec _ _)) in H4. apply H3 in H4 as P2.
        destruct (equal x u); destruct (equal x v); subst.
        + erewrite -> NMap.FindReplaceEq. lia.
        + erewrite -> NMap.FindReplaceEq; erewrite -> NMap.FindReplaceNeq. 
        - assert ((l [v0]) <= l [v])%nat. { apply H5. + edestruct R; eauto. + unfold res_cap.
        rewrite H1. eapply (reflect_iff _ _ (QLt_spec _ _)).
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2. lra.
        } lia.
        - symmetry. auto.
        + erewrite -> NMap.FindReplaceEq; erewrite -> NMap.FindReplaceNeq.
        - lia.
        - symmetry; auto.
        + erewrite -> NMap.FindReplaceNeq. 
        - erewrite -> NMap.FindReplaceNeq. lia. symmetry; auto.
        - symmetry; auto.
        + auto.
    Qed.

    Lemma FPNCondition fn f l u vs': 
        (u ∈v nodes fn) = true -> forall v, 
        ValidLabeling fn f l -> ActiveNode fn f u ->
        find_push_node fn f l u vs' = Some v -> PushCondition fn f l u v.
        Proof.
            unfold PushCondition, ValidLabeling, ActiveNode. intros. 
            destruct fn as [[[[vs es] c] s] t]. split.
            + apply H1; apply H.
            + induction vs'. 
            - simpl in H2; inversion H2.
            - simpl in H2. destruct_guard_in H2.
            * apply andb_prop in E0. destruct E0. inversion H2. subst.
            eapply (reflect_iff _ _ (Nat.eqb_spec _ _)) in H3. lia.
            * apply IHvs'. apply H2.
            Qed.

    Lemma SumSame (f:@EMap.t Q 0) (s:V->V*V) vs u v d : 
        (forall v0,  v0 ∈v vs = true -> s v0 <> (u, v)) ->
        map (fun v0 => @EMap.find Q 0 
            (EMap.update (u, v) (fun x0 => x0 + d) f) 
            (s v0)) vs = 
        map (fun v0 => @EMap.find Q 0 f (s v0)) vs.
        Proof.
            induction vs; intros.
            + simpl. auto.
            + simpl. erewrite IHvs; auto.
            f_equal. clear IHvs. erewrite EMap.FindUpdateNeq.
            - auto.
            - apply H. cbn. rewrite eqb_refl. auto.
            - intros. apply H. cbn. destruct_guard; auto.
            Qed.
    
    Lemma PushActiveCondition (fn:FlowNet) (f:@EMap.t R 0) u v x: 
        ActiveNode fn f x -> x<>v -> x<>u -> ActiveNode fn (push fn f u v) x .
        Proof.
            unfold ActiveNode. destruct fn as [[[[vs es] c] s] t]. intros.
            unfold push. destruct ((u, v) ∈e es) eqn : E.
            + unfold excess. set (d := Qmin _ _). rewrite SumSame.
            - rewrite SumSame.
            * apply H. 
            * intros v0 _ q. inversion q. subst. apply H1. auto.
            - intros v0 _ q. inversion q. subst. apply H0. auto. 
            +  set (d := Qmin _ _). unfold excess. unfold Qminus. rewrite SumSame.
            - rewrite SumSame.
            * apply H.
            * intros v0 _ q. inversion q. subst. apply H0. auto.
            - intros v0 _ q. inversion q. subst. apply H1. auto. 
        Qed.


    Lemma DeltaPositive fn (f:@EMap.t Q 0) (l:@NMap.t nat O) u v:
        let '((vs, es),c,s,t) := fn in
        (u ∈v vs) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f -> 
        PushCondition fn f l u v ->
        Qmin (excess fn f u) (res_cap fn f u v) >= 0.
        Proof.
            unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
            destruct fn as [[[[vs es] c] s] t]. unfold CapacityConstraint, NonDeficientFlowConstraint.
            intros. destruct H2. edestruct (Q.min_spec_le); destruct H4; rewrite H5; try lra.
            unfold res_cap. destruct ((u, v) ∈e es) eqn : E.
            + destruct H1. specialize (H1 _ _ E). unfold R in *. lra.
            + apply H0.
            Qed.

    Lemma PushFlowMapPos fn (f:@EMap.t Q 0) (l:@NMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        (x ∈v vs) = true ->
        FlowMapPositiveConstraint fn f -> 
        PreFlowCond fn f ->
        PushCondition fn f l x y ->
        FlowMapPositiveConstraint fn (push fn f x y).
        Proof.
            unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
            unfold CapacityConstraint, NonDeficientFlowConstraint.
            destruct fn as [[[[vs es] c] s] t]. intros. split.
            + unfold push. destruct ((x, y) ∈e es) eqn : E.
            - destruct (Edge.equal (x,y) (u,v)).
            * inv_clear e. rewrite EMap.FindUpdateEq.
            eapply (DeltaPositive ((vs, es),c,s,t)) in H2; auto.
            specialize (H0 u v). lra.
            * rewrite EMap.FindUpdateNeq; auto.
            apply H0.
            - destruct (Edge.equal (y,x) (u,v)).
            * inv_clear e. rewrite EMap.FindUpdateEq.
            unfold res_cap. rewrite E. edestruct (Q.min_spec_le); destruct H3.
            ** erewrite H4. unfold R in *. lra.
            ** erewrite H4. unfold R in *. lra.
            * rewrite EMap.FindUpdateNeq; auto.
             apply H0.
             + apply H0.
         Qed.        


    Lemma SumInR (f:@EMap.t Q 0) vs u v d : 
        VSet.IsSet vs ->
        u ∈v vs = true ->
        QSumList (
            map (fun v0 => @EMap.find Q 0 
                  (EMap.update (u, v) (fun x0 => x0 + d) f) 
                  (v0, v)) vs) == 
        QSumList (map (fun v0 => @EMap.find Q 0 f (v0, v)) vs) + d.
    Proof. 
        induction vs; intros.
        + simpl. inversion H0.
        + simpl. destruct (equal u a).
        - subst. rewrite EMap.FindUpdateEq. erewrite SumSame.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. inv_clear H. rewrite H1 in H4. inversion H4.
        - rewrite EMap.FindUpdateNeq.
        * erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        ** simpl in H0. rewrite eqb_neq in H0; auto.
        * intro C. inv_clear C. apply n. reflexivity.
        Qed. 

    Lemma SumInL (f:@EMap.t Q 0) vs: forall u v d,
        VSet.IsSet vs ->
        v ∈v vs = true ->
        QSumList (
            map (fun v0 => @EMap.find Q 0 
                  (EMap.update (u, v) (fun x0 => x0 + d) f) 
                  (u,v0)) vs) == 
        QSumList (map (fun v0 => @EMap.find Q 0 f (u,v0)) vs) + d.
    Proof.
        induction vs; intros.
        + simpl. inversion H0.
        + simpl. destruct (equal v a).
        - subst. rewrite EMap.FindUpdateEq. erewrite SumSame.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. inv_clear H. rewrite H1 in H4. inversion H4.
        - rewrite EMap.FindUpdateNeq.
        * erewrite IHvs.
        ** lra.
        ** inversion H. subst. auto.
        ** simpl in H0. rewrite eqb_neq in H0; auto.
        * intro C. inv_clear C. apply n. reflexivity.
        Qed.

    (* pikk tõestus paljude hargnemistega. 
        * Qmin-ist saab lahti kasutades Q.min_spec 
        * summade puhul Sum* (enne vastavad destruct (equal x y)...) *)
    Lemma PushPreFlow fn (f:@EMap.t Q 0) (l:@NMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        VSet.IsSet vs ->
        (x ∈v vs) = true ->
        (y ∈v vs) = true ->
        PreFlowCond fn f -> 
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l x y->
        PreFlowCond fn (push fn f x y).
    Proof.
        unfold PreFlowCond, FlowMapPositiveConstraint, PushCondition, PreFlowCond.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros Hvs Hxvs Hyvs [Hcc Hndf] Hfmp Hpc.
        split.
        + intros. unfold push. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)). 
        * inv_clear e. rewrite EMap.FindUpdateEq. unfold res_cap.
        rewrite E. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. unfold R in *. lra.
        ** erewrite H1. unfold R in *. lra.
        * rewrite EMap.FindUpdateNeq; auto.
        - unfold res_cap. rewrite E. destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e. rewrite EMap.FindUpdateEq. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. specialize (Hcc _ _ H). lra.
        ** rewrite H1. specialize (Hfmp u v). unfold R in *. lra.
        * rewrite EMap.FindUpdateNeq; auto.
        + intros. eapply (DeltaPositive ((vs, es),c,s,t)) in Hpc as HDp; auto;
        [| unfold PreFlowCond, CapacityConstraint, NonDeficientFlowConstraint; tauto].        
        unfold push, res_cap in *. destruct ((x, y) ∈e es) eqn : E.
        - unfold excess at 1. destruct (equal v y). 
        * subst. destruct (equal x y).
        ** subst. rewrite SumInR; auto.
        rewrite SumInL; auto. destruct Hpc. unfold excess in H1.
        unfold R in *. lra.
        ** rewrite SumInR; auto. 
        rewrite SumSame.
        **** specialize (Hndf y H H0). unfold excess in Hndf.
         unfold R in *. lra.
         **** intros. intro C. inv_clear C. apply n. reflexivity.
         * unfold excess in Hpc. destruct (equal x v). 
         ** subst. rewrite SumSame. 
         *** erewrite SumInL; auto.
          edestruct (Q.min_spec_le); destruct H1.
         **** erewrite H2 in *. unfold excess. unfold R in *. lra.
         **** erewrite H2 in *. unfold excess in H1. unfold R in *. lra.
         *** intros. intro C. inv_clear C. apply n. reflexivity.
         ** rewrite SumSame, SumSame.
         *** apply Hndf in H; auto.
         *** intros. intro C. inv_clear C. apply n0. reflexivity.
         *** intros. intro C. inv_clear C. apply n. reflexivity.  
         - unfold excess. unfold Qminus. destruct (equal v x).
         * subst. destruct (equal x y).
         ** subst. erewrite SumInL; auto.
         erewrite SumInR; auto.
         unfold excess in Hpc. unfold R in *. lra.
         ** erewrite SumInR; auto.
         erewrite SumSame.
         *** unfold excess in Hpc, HDp.
         edestruct (Q.min_spec_le); destruct H1.
         **** erewrite H2 in *. unfold R in *. lra.
         **** erewrite H2 in *. unfold R in *. lra.
         *** intros. intro C. inv_clear C. apply n. reflexivity.
         * destruct (equal v y).
         ** subst. erewrite SumInL; auto.
         rewrite SumSame.
         *** apply Hndf in H; auto.
         unfold excess in H. unfold excess, Qminus in HDp. unfold R in *. lra.
        *** intros. intro C. inv_clear C. apply n. reflexivity.
        ** erewrite SumSame, SumSame.
        *** apply Hndf in H; auto.
        *** intros. intro C. inv_clear C. apply n0. reflexivity.
        *** intros. intro C. inv_clear C. apply n. reflexivity.
        Qed.


    Lemma FPNinVs fn f l u v vs': 
    find_push_node fn f l u vs' = Some v -> (v ∈v vs') = true.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. induction vs'; intros.
        + simpl in H. inversion H.
        + simpl in H. destruct_guard_in H.
        - inversion H. subst. simpl. rewrite eqb_refl. reflexivity.
        - simpl. destruct (equal v a); auto.
        Qed.

    Lemma HENSCondition fn v :forall (f:@EMap.t Q 0),
        has_excess_not_sink fn f v = true -> 0 < excess fn f v /\ v <> sink fn.
    Proof.
        unfold has_excess_not_sink. destruct fn as [[[[vs es] c] s] t].
        intros. destruct (equal v t) in H. subst.
        + inversion H.
        + destruct_guard_in H.
        - eapply (reflect_iff _ _ (QLt_spec _ _)) in E0. split; auto.
        - inversion H. 
    Qed.

    Lemma PushActiveInv (fn:FlowNet) (f:@EMap.t R 0) (l:@NMap.t nat O) u v x:
        VSet.IsSet (nodes fn) ->
        u ∈v nodes fn = true ->
        v ∈v nodes fn = true ->
        x<>v ->
        PreFlowCond fn f ->
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l u v ->
        ActiveNode fn (push fn f u v) x ->
        ActiveNode fn f x.
    Proof.
        unfold ActiveNode, push, PreFlowCond, 
        FlowConservationConstraint, PushCondition.
        destruct fn as [[[[vs es] c] s] t].
        intros. destruct_guard_in H6.
        + destruct H6. split; auto. 
        unfold excess in *.
        destruct (equal x u) in H7.
        - subst. erewrite SumSame, SumInL in H7; auto.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        - erewrite SumSame, SumSame in H7.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply n. reflexivity.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        + destruct H6. split; auto. 
        unfold excess in *. unfold Qminus in *. set (d:= Qmin _ _) in *.
        destruct (equal x u) in H7.
        - subst. erewrite SumInR, SumSame in H7; auto.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        - erewrite SumSame, SumSame in H7; auto.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        * intros. intro C. inv_clear C. apply n. reflexivity.
        Qed.
        
    Lemma FPNConditionNone fn f l u vs': 
        find_push_node fn f l u vs' = None -> 
        forall v, v ∈v vs' = true -> (0 <? res_cap fn f u v = false) 
        \/ (l[u] <> l[v] + 1)%nat.
    Proof.
        induction vs'; intros.
        + inversion H0.
        + simpl in *. destruct fn as [[[[vs es] c] s] t]. 
        destruct (equal v a) in H0. subst.
        - clear H0. destruct_guard_in H.
        * inversion H.
        * apply andb_false_iff in E0. destruct E0.
        ** apply Nat.eqb_neq in H0. right. lia.
        ** left. auto.
        - destruct_guard_in H.
        * inversion H.
        * eapply IHvs' in H; eauto.
        Qed. 

    Lemma HENSConditionFalse fn v :forall (f:@EMap.t Q 0),
        has_excess_not_sink fn f v = false -> 0 >= excess fn f v \/ v = sink fn.
    Proof.
        unfold has_excess_not_sink.
        intros. destruct fn as [[[[vs es] c] s] t].
        destruct (equal v t). subst.
        + clear H. right. auto.
        + destruct_guard_in H.
        - inversion H.
        - clear H. apply QLt_false in E0. tauto.
        Qed.

    Lemma PushNoSteepArc fn f l x y:
        (x ∈v nodes fn) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f -> 
        PushCondition fn f l x y ->
        NoSteepArc fn f l -> NoSteepArc fn (push fn f x y) l.
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition,
        NoSteepArc. unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros. unfold push in H4. set (d:= Qmin _ _) in H4. 
        destruct ((x, y) ∈e es) eqn : E.
        + unfold res_cap in H4. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e. lia.
        * apply H3. unfold res_cap. rewrite E2. rewrite EMap.FindUpdateNeq in H4; auto.
        - destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e. lia.
        * rewrite EMap.FindUpdateNeq in H4; auto. 
        apply H3. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H4. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e. lia.
        * rewrite EMap.FindUpdateNeq in H4; auto.
        apply H3. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e. lia.
        * rewrite EMap.FindUpdateNeq in H4; auto.
        apply H3. unfold res_cap. rewrite E2. auto.
        Qed.

    Lemma PushResCapNodes fn f x y:        
        x ∈v (nodes fn) = true -> y ∈v (nodes fn) = true ->
        ResCapNodes fn f -> ResCapNodes fn (push fn f x y).
    Proof.
        unfold ResCapNodes.
        intros. unfold push in H2. destruct fn as [[[[vs es] c] s] t].
        set (d:= Qmin _ _) in H2. destruct ((x, y) ∈e es) eqn : E.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        -  destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        Qed.
    
    Lemma RelabelNoSteepArc fn f l x:
        (x ∈v nodes fn) = true -> 
        ResCapNodes fn f ->
        find_push_node fn f l x (nodes fn) = None ->
        NoSteepArc fn f l -> 
        forall l', relabel fn f l x = Some l' -> NoSteepArc fn f l'.
    Proof.
        unfold ResCapNodes, NoSteepArc, relabel.
        destruct fn as [[[[vs es] c] s] t].
        intros. destruct_guard_in H3; [| inversion H3].
        inv_clear H3. apply RFindCondition in E0.
        destruct (equal x u), (equal x v).
        + subst. rewrite NMap.FindReplaceEq. lia.
        + subst. rewrite NMap.FindReplaceEq. rewrite NMap.FindReplaceNeq; auto.
        destruct E0. apply H0 in H4 as P. destruct P as [P1 P2].
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H4.
        apply H5 in H4; auto. lia.
        + subst. rewrite NMap.FindReplaceEq. rewrite NMap.FindReplaceNeq; auto.
        destruct E0 as [E1 E2]. eapply (reflect_iff _ _ (QLt_spec _ _)) in E1. 
        apply H0 in E1 as P. destruct P as [P1 P2]. 
        apply H2 in H4. apply H2 in E1. lia.
        + rewrite NMap.FindReplaceNeq; auto. rewrite NMap.FindReplaceNeq; auto.
        Qed.

    Lemma RelabelValidCondition fn f l u : 
        ActiveNode fn f u ->
        NoSteepArc fn f l ->
        find_push_node fn f l u (nodes fn) = None -> 
        forall v,
        relabel_find fn f l u (nodes fn) = Some v -> 
        RelabelCondition fn f l u.
    Proof.
        unfold ActiveNode, NoSteepArc, RelabelCondition.
        destruct fn as [[[[vs es] c] s] t]. intros.
        split; try tauto. intros.
        eapply RFindCondition in H2 as P2. destruct P2. apply H0 in H4 as P1.
        eapply RFindMemCondition in H2.
        eapply FPNConditionNone with (v := v0) in H1; auto. 
        destruct H1.
        + rewrite QLt_false in H1. lra.
        + lia.
        Qed.

    Lemma FlowConservationGpr fn g:forall (f:@EMap.t Q 0) (l:@NMap.t nat O) ac tr,
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        VSet.IsSet vs ->
        VSet.IsSet ac ->
        ResCapNodes fn f ->
        NoSteepArc fn f l ->
        (forall n, n ∈v ac = true -> n ∈v vs = true) ->
        ValidLabeling fn f l ->
        (forall n, n ∈v ac = true <-> (ActiveNode fn f n /\ n<>t)) ->
        PreFlowCond fn f ->
        FlowMapPositiveConstraint fn f ->
        forall f' tr', 
        gpr_helper_trace fn f l ac g tr = (Some f',tr') ->
        (forall n, ActiveNode fn f' n -> n=t) /\ 
        FlowConservationConstraint fn f'.
    Proof.        
        destruct fn as [[[[vs es] c] s] t]. induction g;
        intros f l ac tr Heisn Hvs Hac Hrcn Hnsa Hnvs Hvl Han Hprc Hfmpc f' tr' H.
        + simpl in H. inversion H.
        + rewrite gpr_helper_trace_fn in H. destruct_guard_in H.
        - destruct p. destruct_guard_in H.
        * cbn zeta in H. destruct_guard_in H.
        ** apply VSet.choiceSome in E0. destruct E0. destruct H1.
         eapply IHg in H; eauto.
        *** clear H IHg. destruct_guard.
        **** apply VSet.AddIsSet. auto.
        **** apply VSet.AddIsSet; auto.
        *** clear H IHg. apply PushResCapNodes; auto.
        **** apply FPNinVs in E1. auto.
        *** clear H IHg. apply PushNoSteepArc; auto.
        eapply FPNCondition; eauto.
        apply Han in H0. tauto.
        *** clear H IHg. intros. destruct_guard_in H. simpl VSet.mem in H.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        ***** rewrite VSet.MemRemoveNeq in H; auto.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        ***** rewrite VSet.MemAddNeq in H; auto. subst.
        destruct (equal n v).
        ****** subst. rewrite VSet.MemRemoveEq in H. inversion H.
        ****** rewrite VSet.MemRemoveNeq in H; auto.
        *** clear H IHg. eapply (PushValidLabel (vs, es, c ,s, t)); auto.
        eapply FPNCondition; eauto. apply Han in H0. tauto.
        *** intros. split; intros.
        **** destruct (equal n v0).
        ***** subst. clear H IHg. apply HENSCondition in E2. split; try tauto.
        split.
        ****** eapply FPNinVs in E1. auto.
        ****** tauto.
        ***** clear H IHg. rewrite VSet.MemAddNeq in H3; eauto.
        destruct_guard_in H3.
        ****** eapply Han in H3. destruct H3. split; eauto.
        destruct (equal n v). subst.
        *******  eapply (reflect_iff _ _ (QLt_spec _ _)) in E0. split; eauto.
        ******* eapply PushActiveCondition; eauto.
        ****** subst. destruct (equal n v).
        ******* subst. rewrite VSet.MemRemoveEq in H3. inversion H3.
        ******* rewrite VSet.MemRemoveNeq in H3; eauto. 
        eapply Han in H3. destruct H3. split; eauto. 
         eapply PushActiveCondition; eauto.
        **** clear H IHg. destruct (equal n v0).
        ***** subst. simpl. rewrite eqb_refl. auto.
        ***** rewrite VSet.MemAddNeq; auto.
        destruct_guard.
        ****** eapply Han. destruct H3. split; auto. destruct (equal n v).
        ******* subst. eapply Han in H0. tauto.
        ******* eapply PushActiveInv in H; auto. 
        ******** eapply FPNinVs in E1. auto.
        ******** eapply FPNCondition in E1; eauto.
        apply Han in H0; tauto.
        ****** subst. rewrite VSet.MemRemoveNeq.
        ******* eapply FPNinVs in E1 as P. eapply FPNCondition in E1; eauto;
        [| eapply Han in H0; tauto]. destruct H3. eapply PushActiveInv in H; eauto.
        eapply Han. split; auto.
        ******* intro C. subst. destruct H3. destruct H. apply QLt_false in E0. lra.
        *** clear H IHg. eapply (PushPreFlow (vs, es, c, s, t)); auto. 
        **** eapply FPNinVs in E1. auto.
        **** eapply FPNCondition; eauto. eapply Han in H0; tauto.
        *** clear H IHg. eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        eapply FPNCondition; eauto. eapply Han in H0. tauto.
        *** auto.
        ** eapply VSet.choiceSome in E0 as P; auto. destruct P. destruct H1.
        eapply FPNinVs in E1 as P. apply Han in H0 as W. destruct W. 
        eapply FPNCondition in E1 as P2; auto.
        eapply HENSConditionFalse in E2 as Q.
        eapply IHg in H; eauto.
        *** eapply VSet.RemoveIsSet. destruct_guard; auto.
        *** eapply PushResCapNodes; auto.
        *** eapply PushNoSteepArc; auto.
        *** intros. destruct (equal n v0).
        **** subst. auto.
        **** rewrite VSet.MemRemoveNeq in H5; auto. eapply Hnvs.
         destruct_guard_in H5; auto. subst. rewrite VSet.MemRemoveNeq in H5; auto.
         intro C. subst. rewrite VSet.MemRemoveEq in H5. inversion H5.
        *** eapply (PushValidLabel (vs, es, c, s, t)); eauto.
        *** intros. destruct (equal n v0).
        **** subst. rewrite VSet.MemRemoveEq. split; intros; [inversion H1 |].
        destruct Q.
        ***** destruct H1. destruct H1. lra.
        ***** simpl in H5. tauto.
        **** rewrite VSet.MemRemoveNeq; auto. destruct_guard; split; intros.
        ***** eapply Han in H5. destruct H5. split; auto. destruct (equal n v).
        ****** subst. split; auto.  eapply (reflect_iff _ _ (QLt_spec _ _)) in E3.
        auto.
        ****** eapply PushActiveCondition; eauto.
        ***** eapply Han. destruct H5. split; auto.
        eapply PushActiveInv in P2; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. rewrite VSet.MemRemoveEq in H5. inversion H5.
        ****** rewrite VSet.MemRemoveNeq in H5; auto. 
        eapply Han in H5. destruct H5. split; auto. 
        eapply PushActiveCondition; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. eapply QLt_false in E3. destruct H5, H1. lra.
        ****** rewrite VSet.MemRemoveNeq; auto. eapply Han. destruct H5. split; auto.
        eapply PushActiveInv in P2; eauto.
        *** eapply (PushPreFlow (vs, es, c, s, t)); eauto.
        *** eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        * destruct_guard_in H.
        ** eapply VSet.choiceSome in E0; auto. destruct E0, H1.
         eapply IHg in H; eauto.
        *** eapply RelabelNoSteepArc; eauto.
        *** eapply (RelabelValidLabel (vs, es, c, s, t)); eauto. 
        unfold relabel in E2. destruct_guard_in E2; [| inversion E2].
        eapply RelabelValidCondition; eauto.
        **** apply Han. auto.
        ** inversion H.
        - apply VSet.choiceNone in E0. subst. inv_clear H. split.
        * intros. destruct (equal n t); auto. assert (n ∈v VSet.empty = true).
        ** eapply Han. tauto.
        ** simpl in H0. inversion H0.
        * unfold FlowConservationConstraint. intros. unfold PreFlowCond in Hprc.
        destruct Hprc. unfold NonDeficientFlowConstraint in H3.
        apply H3 in H as P; auto. clear IHg. 
        destruct (Qeq_bool (excess (vs, es, c, s, t) f' v) 0) eqn : E.
        ** eapply Qeq_bool_iff in E. auto.
        ** eapply Qeq_bool_neq in E. assert (v ∈v VSet.empty = true).
        *** eapply Han. split; auto. split; auto. lra.
        *** inversion H4.
        Qed.

    (* sama nagu SumSameUpdate *)
    Lemma SumSameReplace (f:@EMap.t Q 0) (s:V->V*V) vs u v d : 
        (forall v0, v0 ∈v vs = true -> s v0 <> (u, v)) ->
        map (fun v0 => @EMap.find Q 0 
            (EMap.replace (u, v) d f) 
            (s v0)) vs = 
        map (fun v0 => @EMap.find Q 0 f (s v0)) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        + simpl. rewrite IHvs; auto.
        f_equal. clear IHvs.
        - erewrite EMap.FindReplaceNeq; auto.
        apply H. cbn. rewrite eqb_refl. auto.
        - intros. apply H. cbn. destruct_guard; auto.
        Qed.

    (* equal y s, siis equal n y, siis equal a s  *)
    Lemma NDFinitial vs es c s t d  y n f: 
        EMap.find f (s,y) <= d ->
        n<>s ->
        excess (vs, es, c, s, t) f n <= 
            excess (vs, es, c, s, t) (EMap.replace (s, y) d f) n .
    Proof.
        intros Hd Hnns.
        induction vs; intros.
        + simpl. lra. 
        + unfold excess in *. simpl. destruct (equal n y).
        - subst. destruct (equal a s).
        * subst. erewrite EMap.FindReplaceEq. erewrite EMap.FindReplaceNeq.
        ** unfold R in *. lra.
        ** intro C. inv_clear C. auto.
        * erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
        ** unfold R in *. lra.
        ** intro C. inv_clear C. auto.
        ** intro C. inv_clear C. auto.
        - erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
        * lra.
        *  intro C. inv_clear C. auto.
        * intro C. inv_clear C. auto.
        Qed.

    (* ind. üle vs *)
    Lemma SourceDeficient vs es c s t y f: 
        (forall a, @EMap.find R 0 f (a,s) <= @EMap.find R 0 f (s,a)) ->
        EMap.find f (s,y) <= c s y ->
        excess (vs, es, c, s, t) (EMap.replace (s, y) (c s y) f) s <= 0.
    Proof.
        intros Has Hcap.
        induction vs; intros.
        + simpl. lra.
        + unfold excess in *. simpl. destruct (Edge.equal (s,y) (a,s)).
        - inv_clear e. erewrite EMap.FindReplaceEq. lra.
        - destruct (equal y a).
        * subst. erewrite EMap.FindReplaceEq. erewrite EMap.FindReplaceNeq.
        ** specialize (Has a). lra.
        ** auto.
        * erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
        ** specialize (Has a). lra.
        ** intro C. inv_clear C. auto.
        ** auto.
        Qed.

    (* väga lühike, kuna võrratused antud. Ind. üle vs.  *)
    Lemma ExcessSame vs es c s t y f n: 
        (forall a, EMap.find f (a,s) <= EMap.find f (s,a)) ->
        EMap.find f (s,y) <= c s y ->
        n<>s ->
        n<>y ->
        excess (vs, es, c, s, t) f n  == excess (vs, es, c, s, t) (EMap.replace (s, y) (c s y) f) n.
    Proof.
        intros Has Hcap Hnns Hnny.
       induction vs; intros.
       + simpl. reflexivity.
       + simpl.  erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
       - unfold excess in IHvs. lra.
       - intro C. inv_clear C. auto.
       - intro C. inv_clear C. auto.
       Qed.

    (* induktsioon üle es'  *)
    Lemma InitialGpr fn :
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        VSet.IsSet vs ->
        forall es' f f' ac ac' ,
        (forall n, n ∈e es' = true -> n ∈e es = true) ->
        VSet.IsSet ac ->
        (forall a, EMap.find f (a,s) <= EMap.find f (s,a)) ->
        (excess fn f s <= 0) ->
        ResCapNodes fn f ->
        (forall n, n ∈v ac = true -> n ∈v vs = true) ->
        (forall n, n ∈v ac = true <-> (ActiveNode fn f n /\ n<>t)) ->
        PreFlowCond fn f ->
        FlowMapPositiveConstraint fn f ->
        initial_push fn f ac es' = (f',ac') ->
        VSet.IsSet ac' /\
        ResCapNodes fn f' /\
        (forall n, n ∈v ac' = true -> n ∈v vs = true) /\
        (forall n, n ∈v ac' = true <-> (ActiveNode fn f' n /\ n<>t)) /\
        PreFlowCond fn f' /\
        FlowMapPositiveConstraint fn f'.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. intros Heisn Hvs es'. 
        induction es';
        intros f f' ac ac' HeisE Hac Haiss Hexc Hrcn Hnvs Hactn Hpfc Hfmpc H.
        + simpl in H. inv_clear H. repeat split; eauto.
        - apply Hrcn in H. tauto.
        - apply Hrcn in H. tauto.
        - eapply Hactn, H.
        - eapply Hactn, H.
        - intros. eapply Hactn in H. apply H.
        - destruct Hpfc; auto.
        - destruct Hpfc; auto.
        - eapply Hfmpc.
        - eapply Hfmpc.
        + unfold initial_push in H. fold initial_push in H. destruct_guard_in H.
        assert (Hvv0 : (v, v0) ∈e es = true). 
        {eapply HeisE. simpl. do 2 rewrite eqb_refl. auto. } 
        destruct (equal s v).
        - subst. eapply IHes' in H; eauto.
        * intros. eapply HeisE. simpl. destruct (Edge.equal n (v, v0)); eauto.
        * destruct_guard; eauto. eapply VSet.AddIsSet; auto.
        * intros. destruct (Edge.equal (v, v0) (a, v)).
        ** inv_clear e. lra.
        ** erewrite EMap.FindReplaceNeq; auto. destruct (equal a v0).
        *** subst. erewrite EMap.FindReplaceEq. 
        assert (EMap.find f (v, v0) <= c v v0).
        **** eapply Hpfc. auto.
        **** specialize (Haiss v0). lra.
        *** erewrite EMap.FindReplaceNeq; eauto. intro C. inv_clear C. auto.
        * eapply SourceDeficient; eauto. eapply Hpfc. auto.
        * unfold ResCapNodes. intros. clear IHes'. unfold res_cap in H0.
        destruct_guard_in H0; eauto. destruct (Edge.equal (v, v0) (v1, u)).
        ** inv_clear e. eapply Heisn in Hvv0. tauto.
        ** erewrite EMap.FindReplaceNeq in H0; eauto.
        eapply Hrcn. unfold res_cap. rewrite E0. apply H0.
        * intros. destruct_guard_in H0; eauto. destruct (equal n v0).
        ** subst. clear IHes'. eapply Heisn. eapply Hvv0.
        ** clear IHes'. eapply Hnvs. rewrite VSet.MemAddNeq in H0; eauto.
        * intros. destruct_guard.
        ** split; intros.
        *** destruct (equal n v0).
        **** subst. clear IHes'. eapply HENSCondition in E0. 
        destruct E0; split; eauto. split; eauto. eapply Heisn, Hvv0.
        **** erewrite VSet.MemAddNeq in H0; eauto.
        clear IHes'. eapply Hactn in H0. destruct H0; split; auto. split.
        ***** eapply Hnvs. eapply Hactn. split; auto.
        ***** assert (EMap.find f (v, v0) <= c v v0).
        ****** eapply Hpfc. auto.
        ****** eapply (NDFinitial vs es c v t) with (n := n) in H2.
        ******* destruct H0. set (e := excess _) in *.  unfold R in *. lra.
        ******* intro C. inv_clear C. destruct H0. lra.
        *** destruct (equal n v0).
        **** subst. simpl. rewrite eqb_refl. auto. 
        **** erewrite VSet.MemAddNeq; eauto. destruct H0. eapply Hactn.
        split; auto. destruct H0. split; auto. 
        assert (EMap.find f (v, v0) <= c v v0). 
        ***** eapply Hpfc. auto.
        ***** destruct (equal n v).
        ****** subst. eapply (SourceDeficient vs es c v t) in H3; eauto.
        set (e := excess _) in *. lra.
        ****** eapply (ExcessSame vs es c v t) in H3; eauto.
        set (e := excess _) in *. lra.
        ** split; intros.
        *** eapply Hactn in H0 as P. destruct P. split; auto.
        split; eauto. destruct (equal n v0).
        **** subst. destruct H1. eapply HENSConditionFalse in E0.
        destruct (equal v0 v).
        ***** subst. assert (EMap.find f (v, v) <= c v v).
        ****** eapply Hpfc; auto.
        ****** eapply (SourceDeficient vs es c v t) in H4; eauto.
        set (e := excess _) in *. lra.
        ***** assert (EMap.find f (v, v0) <= c v v0).
        ****** eapply Hpfc; auto.
        ****** eapply (NDFinitial vs es c v t) with (n := v0) in H4; eauto.
         set (e := excess _) in *. lra.
        **** destruct (equal n v).
        ***** subst. assert (EMap.find f (v, v0) <= c v v0). 
        ****** eapply Hpfc; auto.
        ****** eapply (SourceDeficient vs es c v t) in H3; eauto. destruct H1.
        set (e := excess _) in *. lra.
        *****  assert (EMap.find f (v, v0) <= c v v0). 
        ****** eapply Hpfc; eauto.
        ****** destruct H1. eapply (ExcessSame vs es c v t) in H3; eauto.
        ******* set (e := excess _) in *. lra.
        *** eapply HENSConditionFalse in E0. destruct H0. eapply Hactn.
        split; auto. destruct H0.
        split; auto. assert (EMap.find f (v, v0) <= c v v0).
        **** eapply Hpfc. clear IHes'. auto. 
    
        **** destruct (equal n v).
        ***** subst. 
        eapply (SourceDeficient vs es c v t) with (y := v0) in Haiss; eauto.
         set (e := excess _) in *. lra.
        ***** destruct (equal n v0).
        ****** subst. destruct E0.
        ******* set (e := excess _) in *. lra.
        ******* contradiction.
        ****** eapply (ExcessSame vs es c v t) with (n := n) in H3; eauto.
        set (e := excess _) in *. lra.
        * unfold PreFlowCond. unfold CapacityConstraint, NonDeficientFlowConstraint.
        split; intros.
        ** destruct (Edge.equal (u, v1) (v, v0)).
        *** inv_clear e. erewrite EMap.FindReplaceEq. lra.
        *** erewrite EMap.FindReplaceNeq; auto.
        eapply Hpfc. auto.
        ** assert (EMap.find f (v, v0) <= c v v0).
        *** eapply Hpfc; auto.
        *** eapply (NDFinitial vs es c v t)  in H2; eauto.
        eapply Hpfc in H0. specialize (H0 H1).  set (e := excess _) in *. lra.
        * unfold FlowMapPositiveConstraint. intros. split.
        ** destruct (Edge.equal (u, v1) (v, v0)).
        *** inv_clear e. erewrite EMap.FindReplaceEq. eapply Hfmpc.
        *** erewrite EMap.FindReplaceNeq; eauto. eapply Hfmpc.
        ** eapply Hfmpc.
        - eapply IHes'; eauto. intros. subst. eapply HeisE. simpl.
        destruct_guard; auto.
        Qed.


    (* e' on juba töödeldud servade hulk.
       induktsioon üle e'', 
        kui e'' = a::e''', siis kasuta ihs (e':= add a e')  *)
    Lemma InitialPushResCap0 vs es c s t e'' : forall e' f f' ac ac',
        (forall e, (e ∈e e' = true \/ e ∈e e'' = true) <-> e ∈e es = true) ->
        (forall v, (s,v) ∈e es = false -> res_cap (vs,es,c,s,t) f s v == 0) ->
        (forall v, (s,v) ∈e e' = true -> res_cap (vs,e',c,s,t) f s v == 0) ->
        initial_push (vs,es,c,s,t) f ac e'' = (f',ac') ->
        forall v, res_cap (vs,es,c,s,t) f' s v == 0.
    Proof.
        induction e''; intros.
        + simpl in H2. inv_clear H2. unfold res_cap. destruct_guard.
        - eapply H in E0. destruct E0.
        * eapply H1 in H2 as P. unfold res_cap in P. rewrite H2 in P. auto.
        * inversion H2.
        - eapply H0 in E0 as P. unfold res_cap in P. rewrite E0 in P. auto.
        + simpl in H2. destruct_guard_in H2. subst. destruct (equal s v0).
        - subst. eapply IHe'' with (e' := ESet.add (v0, v1) e') in H2; eauto.
        * intros. clear IHe'' H2. destruct (Edge.equal e (v0, v1)).
        ** inv_clear e. erewrite ESet.MemAddEq. split; intros.
        *** eapply H. right. simpl. rewrite eqb_refl, eqb_refl. auto.
        *** tauto.
        ** erewrite ESet.MemAddNeq; auto. split; intros.
        *** eapply H. destruct H2.
        **** tauto.
        **** right. simpl. destruct_guard; auto.
        *** eapply H in H2. simpl in H2. rewrite Edge.eqb_neq in H2; auto.
        * intros. unfold res_cap. rewrite H3. clear H2.
         destruct (Edge.equal (v0, v1) (v2, v0)).
        ** inv_clear e. erewrite EMap.FindReplaceEq. clear IHe''.
        assert ((v2, v2) ∈e es = true).
        *** eapply H. right. simpl. rewrite eqb_refl. auto.
        *** rewrite H3 in H2. inversion H2.
        ** erewrite EMap.FindReplaceNeq; auto. clear IHe''. eapply H0 in H3 as P.
        unfold res_cap in P. rewrite H3 in P. auto.
        * intros. unfold res_cap. rewrite H3. clear H2 IHe''.
        destruct (equal v2 v1).
        ** inv_clear e. rewrite EMap.FindReplaceEq. lra.
        ** rewrite EMap.FindReplaceNeq.
        *** rewrite ESet.MemAddNeq in H3.
        **** eapply H1 in H3 as P. unfold res_cap in P. rewrite H3 in P. auto.
        **** intro C. inv_clear C. destruct n. auto.
        *** intro C.  inv_clear C. destruct n. auto.
        - eapply IHe''  with (e' := ESet.add (v0, v1) e'); intros; eauto.
        *  destruct (Edge.equal e (v0, v1)).
        ** inv_clear e. rewrite ESet.MemAddEq. split; intros.
        *** eapply H. right. simpl. rewrite eqb_refl, eqb_refl. auto.
        *** tauto.
        ** rewrite ESet.MemAddNeq; auto. split; intros.
        *** eapply H. simpl. rewrite Edge.eqb_neq; auto.
        *** eapply H in H3 as P. simpl in P. rewrite Edge.eqb_neq in P; auto.
        * unfold res_cap. rewrite H3. rewrite ESet.MemAddNeq in H3.
        ** eapply H1 in H3 as P. unfold res_cap in P. rewrite H3 in P. auto.
        ** intro C. inv_clear C. destruct n. auto.
        Qed.

    (* rakenda InitialGpr ja InitialPushResCap0, kus e'=nil  *)
    Lemma FlowConservationGprMain fn:
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        VSet.IsSet vs ->
        (forall u v, c u v >= 0) ->
        forall f' tr', 
        gpr_trace fn = (Some f',tr') ->
        (forall n, ActiveNode fn f' n -> n=t) /\ 
        FlowConservationConstraint fn f'.
    Proof.
        destruct fn as [[[[vs es] c] s] t].  intros. unfold gpr_trace in H2.
        destruct_guard_in H2. 
        eapply (InitialGpr (vs, es, c, s, t)) in E0 as P; eauto.
        + destruct P, H4, H5, H6, H7. 
        eapply (FlowConservationGpr (vs, es, c, s, t)) in H2; eauto.
        - simpl. unfold NoSteepArc. intros. simpl. destruct (equal u s).
        * subst. eapply InitialPushResCap0 with (e' := nil) (v := v) in E0.
        ** set (r := res_cap _) in *. lra.
        ** intros. split; intros.
        *** destruct H10; auto. inversion H10.
        *** right. auto.
        ** intros. unfold res_cap. rewrite H10. simpl. reflexivity.
        ** intros. inversion H10.
        * lia.
        - simpl. unfold ValidLabeling. intros. simpl. destruct (equal u s), (equal v s).
        * subst. lia.
        * subst. unfold PR.E in H9. eapply ESet.in_filter in H9. destruct H9.
         eapply InitialPushResCap0 with (e' := nil) (v := v) in E0.
         ** unfold res_cap in E0. rewrite H9 in E0. 
         eapply (reflect_iff _ _ (QLt_spec _ _)) in H10. lra.
         ** intros. split; intros.
         *** destruct H11; auto. inversion H11.
         *** tauto.
         ** intros. unfold res_cap. rewrite H11. simpl. lra.
         ** intros. inversion H11.
         * subst. lia.
         * lia. 
        + eapply VSet.NilIsSet.
        + intros. simpl. lra.
        + unfold excess. clear. induction vs.
        - simpl. lra.
        - simpl. lra.
        + unfold ResCapNodes. intros. unfold res_cap in H3. destruct_guard_in H3.
        - apply H in E1. auto.
        - simpl in H3. lra.
        + intros. inversion H3.
        + intros. split; intros.
        - inversion H3.
        - unfold ActiveNode in H3. destruct H3. destruct H3. simpl in H5.
        clear - H5. induction vs.
        * simpl in H5. lra.
        * simpl in H5. lra.
        + unfold PreFlowCond.  
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        split; intros.
        - simpl. auto.
        - simpl. clear. induction vs; simpl; lra.
        + unfold FlowMapPositiveConstraint. intros; split; auto.
        simpl. lra.
    Qed.

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

