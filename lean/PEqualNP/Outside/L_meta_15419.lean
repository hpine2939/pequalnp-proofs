import PEqualNP.Defs
-- A circuit with NOT gates for f gives, with one more AND gate, a circuit for the seven-input
-- function f(x0..x5) AND x6 (namespace Lift). For that function a new base case of the exhaustive
-- checker copied from the checked proof of L-meta-982 shows the lower bound; its data were
-- computed for this function. An AND/OR circuit of the matching size closes the row.
namespace PEqualNP.Outside.L_meta_15419_aux
lemma bFT:(false=true)=False:=Bool.false_eq_true
lemma bTA {b:Bool}:(true&&b)=b:=Bool.true_and b
lemma bOT {a b:Bool}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma bAT {a b:Bool}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma bNF:(!false)=true:=Bool.not_false
lemma bNT {b:Bool}:((!b)=true)=(b=false):=Bool.not_eq_true' b
lemma lAA {α:Type _} (l1 l2 l3:List α):(l1++l2)++l3=l1++(l2++l3):=List.append_assoc l1 l2 l3
lemma lMC {α β:Type _} {f : α->β} {a : α} {l:List α}:(a::l).map f=f a::l.map f:=List.map_cons
lemma lMM {α:Type _} {a b : α} {l:List α}:a ∈ b::l ↔ a=b\/a ∈ l:=List.mem_cons
lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma lRC {α:Type _} {a : α} {l:List α}:(a::l).reverse=l.reverse++[a]:=List.reverse_cons
lemma lFC {α β:Type _} {f : α->β->β} {b : β} {a : α} {l:List α}:(a::l).foldr f b=f a (l.foldr f b):=List.foldr_cons
lemma lAL {α:Type _} {p : α->Bool} {l:List α}:l.all p=true ↔ ∀ x ∈ l,p x=true:=List.all_eq_true
lemma lAN {α:Type _} {p : α->Bool} {l:List α}:l.any p=true ↔ ∃ x ∈ l,p x=true:=List.any_eq_true
lemma nTB {n i:Nat}:(2 ^ n - 1).testBit i=decide (i < n):=by simp [Nat.testBit_two_pow_sub_one]
lemma nEQ {x y:Nat} (h:∀ i,x.testBit i=y.testBit i):x=y:=Nat.eq_of_testBit_eq h
lemma nTO {x y i:Nat}:(x|||y).testBit i=(x.testBit i||y.testBit i):=by simp [Nat.testBit_or]
lemma nTA {x y i:Nat}:(x&&&y).testBit i=(x.testBit i&&y.testBit i):=by simp [Nat.testBit_and]
lemma nTX {x y i:Nat}:(x^^^y).testBit i=(x.testBit i ^^ y.testBit i):=by simp [Nat.testBit_xor]
lemma nTS {x k i:Nat}:(x >>> k).testBit i=x.testBit (k+i):=by simp [Nat.testBit_shiftRight]
lemma nLO {x y:Nat}:Nat.lor x y=x|||y:=Nat.lor_eq
lemma nLA {x y:Nat}:Nat.land x y=x&&&y:=Nat.land_eq
lemma nXO {x y:Nat}:Nat.xor x y=x^^^y:=Nat.xor_eq
lemma nZT {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma lMA {α β:Type _} {f : α->β} {l1 l2:List α}:(l1++l2).map f=l1.map f++l2.map f:=List.map_append
lemma lLM {α β:Type _} (f : α->β) {l:List α}:(l.map f).length=l.length:=List.length_map f
lemma lRR {α:Type _} {l:List α}:l.reverse.reverse=l:=List.reverse_reverse l
lemma lANil {α:Type _} {l:List α}:l++[]=l:=List.append_nil l
lemma lSA {α:Type _} {a : α} {l:List α} : [a]++l=a::l:=List.singleton_append
lemma lCA {α:Type _} {a : α} {l1 l2:List α}:(a::l1)++l2=a::(l1++l2):=List.cons_append
lemma lPM {α:Type _} {a : α} {l₁ l₂:List α}:(l₁++a::l₂).Perm (a::(l₁++l₂)):=List.perm_middle
lemma nAC (a b:Nat):a+b=b+a:=Nat.add_comm a b
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma nAZ {a:Nat}:a+0=a:=Nat.add_zero a
lemma nZL (a:Nat) : 0<=a:=Nat.zero_le a
lemma bOS {a:Bool}:(a||a)=a:=Bool.or_self a
lemma bOTR {a:Bool}:(a||true)=true:=Bool.or_true a
lemma bTOR {a:Bool}:(true||a)=true:=Bool.true_or a
lemma bATR {a:Bool}:(a&&true)=a:=Bool.and_true a
lemma bBT {a:Bool}:(a ^^ true)=!a:=Bool.bne_true a
lemma dTR {p:Prop} [Decidable p] (h:p):decide p=true:=decide_eq_true h
lemma n2P (n:Nat) : 0 < 2 ^ n:=Nat.two_pow_pos n
lemma lMp {α β:Type _} {f : α->β} {b : β} {l:List α}:b ∈ l.map f ↔ ∃ a ∈ l,f a=b:=List.mem_map
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma fCD {α β γ:Type _} (f : β->γ) (g : α->β):f ∘ g=fun x => f (g x):=Function.comp_def f g
lemma lPR {α:Type _} (l:List α):l.Perm l:=List.Perm.refl l
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
lemma lPC {α:Type _} (x : α) {l1 l2:List α} (h:l1.Perm l2):(x::l1).Perm (x::l2):=List.Perm.cons x h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev BFn (n : ℕ):=(Fin n->Bool)->Bool
def q3 (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma zd (gs gs':List Gate) (w:List Bool) :
   q3 (gs++gs') w=q3 gs' (q3 gs w):=by
 simp [q3,List.foldl_append]
lemma y1 (gs:List Gate):∀ w:List Bool,
   ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   have:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht];simp
lemma qu (gs:List Gate) (w:List Bool) :
   (q3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=y1 gs w
 rw [ht];simp [hl]
lemma ve (gs:List Gate) (w:List Bool) (i : ℕ) (h:i < w.length) :
   (q3 gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=y1 gs w
 rw [ht,List.getD_append _ _ _ _ h]
def Ok (g:Gate):Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
   (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 . exact List.getD_append _ _ _ _ hj
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
 simp
lemma z2 {α:Type} (L:List α) (S d : α) (k : ℕ) (h:L.length=k) :
   (L++[S]).getD k d=S:=by
 subst h;simp
def yb {n : ℕ} (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
 (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n : ℕ} (l:List ℕ) (F : ℕ->Finset (Fin n)) (i:Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]
lemma kf {n : ℕ} (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
   i ∈ yb L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 q71 _ _ _
def zb {n : ℕ} (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
 gs.foldl (fun L g => L++[yb L g]) L
def qr (n : ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n => {i}
def q207 {n : ℕ} (x y:Fin n->Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
 L.length=w.length/\w.length=w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n : ℕ} (x y:Fin n->Bool) (gs:List Gate) :
   ∀ (L:List (Finset (Fin n))) (w w':List Bool),q207 x y L w w' ->
     q207 x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil => intro L w w' h;exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[yb L g])
     (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w'++[g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0] at hj
     rw [h1,z0,h2,z0]
     congr 1
     apply List.map_congr_left
     intro a ha
     exact h3 a (fun i hi => hj i ((kf L g i).2 ⟨a,ha,hi⟩))
   . rw [q8 _ _ _ _ hjl] at hj
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact h3 j hj
lemma j4 {n : ℕ} (x y:Fin n->Bool) :
   q207 x y (qr n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 . have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [qr,hjn])
   simp [hjn,hx]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
def Cnt {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))):Prop :=
 ∀ W:Finset ℕ,(W.biUnion fun j => L.getD j ∅).card<=t+W.card
lemma q166 {n : ℕ}:Cnt 0 (qr n):=by
 intro W
 refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _
 by_cases hjn:j < n
 . simp [qr,hjn]
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q194 {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))) (g:Gate) (hg:g.inputs.length<=2)
   (h:Cnt t L):Cnt (t+1) (L++[yb L g]):=by
 intro W
 by_cases hW:L.length ∈ W
 . have hsub:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅):=by
     intro i hi
     rw [Finset.mem_biUnion] at hi ⊢
     obtain ⟨j,hjW,hij⟩:=hi
     by_cases hjl:j=L.length
     . subst hjl
       rw [z0] at hij
       obtain ⟨a,ha,hia⟩:=(kf L g i).1 hij
       exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
     . rw [q8 _ _ _ _ hjl] at hij
       exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
   have hc1:(W.erase L.length ∪ g.inputs.toFinset).card<=(W.card - 1)+2:=by
     refine le_trans (Finset.card_union_le _ _) ?_
     rw [Finset.card_erase_of_mem hW]
     exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
   have hWpos : 1<=W.card:=Finset.card_pos.2 ⟨_,hW⟩
   have:=h (W.erase L.length ∪ g.inputs.toFinset)
   have:=Finset.card_le_card hsub
   omega
 . have heq:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       = (W.biUnion fun j => L.getD j ∅):=by
     apply Finset.biUnion_congr rfl
     intro j hj
     exact q8 _ _ _ _ (fun e => hW (e ▸ hj))
   rw [heq]
   have:=h W
   omega
lemma q118 {n : ℕ} (gs:List Gate):∀ (t : ℕ) (L:List (Finset (Fin n))),
   (∀ g ∈ gs,Ok g)->Cnt t L->Cnt (t+gs.length) (zb gs L):=by
 induction gs with
 | nil => intro t L _ h;exact h
 | cons g gs ih =>
   intro t L hok h
   have:=ih (t+1) (L++[yb L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
     (q194 t L g (hok g List.mem_cons_self).2 h)
   rw [lLC,show t+(gs.length+1)=t+1+gs.length by omega]
   exact this
lemma q117 (n : ℕ) (f:(Fin n->Bool)->Bool) (T:Finset (Fin n))
   (hdep:∀ i ∈ T,∃ x:Fin n->Bool,f (Function.update x i (!x i))≠f x)
   (s : ℕ) (h:HasCircuitSize n f s):T.card<=s+1:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set S:=(zb C.gates (qr n)).getD C.output ∅ with hS
 have hall:T ⊆ S:=by
   intro i hiT
   by_contra hi
   obtain ⟨x,hx⟩:=hdep i hiT
   apply hx
   have hag:=(k6 (Function.update x i (!x i)) x C.gates _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠i:=fun e => hi (e ▸ hk)
       simp [fUN this])
   rw [← hev,← hev]
   exact hag
 have hc:=q118 C.gates 0 (qr n) ok q166 {C.output}
 simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc
 rw [← hS] at hc
 have:=Finset.card_le_card hall
 omega
def vg (g:Gate):Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g
lemma q107 (g:Gate) (F : ℕ->Bool) :
   (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g
 cases op <;> simp only [vg]
 cases inputs <;> simp [GateOp.eval]
def NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma q45 (g:Gate) (h:Ok g):NOk (vg g):=by
 obtain ⟨op,inputs⟩:=g
 obtain ⟨hop,hlen⟩:=h
 rcases hop with h | h | h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg] <;> omega
lemma jd (gs:List Gate):∀ w:List Bool,
   q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil => intro w;rfl
 | cons g gs ih =>
   intro w
   have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
       (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
   have s2:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [s1,s2,q107,ih]
abbrev Stat:=Sum Bool ℕ
def ze (w:List Bool):Stat->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false
def qn (m : ℕ):Stat->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m
def wr (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | Sum.inl c::_ => (none,Sum.inl (!c))
 | Sum.inr j::_ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def ko (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def ji (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
 match op with
 | GateOp.and => ko m ins
 | GateOp.or => ji m ins
 | GateOp.not => wr m ins
 | _ => (none,Sum.inl false)
def q161 (m : ℕ) (g:Gate):Prop :=
 (g.op=GateOp.not/\∃ j,j < m/\g.inputs=[j]) \/
 ((g.op=GateOp.and\/g.op=GateOp.or)/\∃ j k,j < m/\k < m/\g.inputs=[j,k])
lemma j2 {m : ℕ} {g:Gate} (h:q161 m g):∀ a ∈ g.inputs,a < m:=by
 rcases h with ⟨_,j,hj,hin⟩ | ⟨_,j,k,hj,hk,hin⟩
 . intro a ha;simp [hin] at ha;omega
 . intro a ha;simp [hin] at ha;rcases ha with rfl | rfl <;> omega
def yq (n : ℕ) (gs:List Gate):Prop :=
 ∀ p g,gs[p]?=some g->q161 (n+p) g
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp [wr] at hg <;> (subst hg;simp [Ok])
 . simp at hg
 . simp at hg
lemma q80 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hv:∀ s ∈ ins,qn m s) :
   ∀ g ∈ (qg op m ins).1,q161 m g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg
   subst hg
   exact Or.inr ⟨Or.inl rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg
   subst hg
   exact Or.inr ⟨Or.inr rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [wr] at hg
   subst hg
   exact Or.inl ⟨rfl,_,hv (Sum.inr _) (by simp),rfl⟩
 . simp at hg
 . simp at hg
lemma jh (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
   (qg op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ko]
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
   (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
   (hv:∀ s ∈ ins,qn w.length s) :
   qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
   ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
     = op.eval (ins.map (ze w)):=by
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
 (acc.1++[(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2++(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
 gs.foldl (qa n) acc
lemma k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
   elim n (g::gs) acc=elim n gs (qa n acc g):=rfl
lemma jz (n : ℕ) (pre post:List Gate) (acc:List Stat × List Gate) :
   elim n (pre++post) acc=elim n post (elim n pre acc):=by
 simp [elim,List.foldl_append]
lemma q50 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
   intro acc
   rw [k4,ih]
   simp only [qa,lLA,lLC,List.length_nil]
   omega
lemma wy (n k : ℕ) (d:Stat) (gs:List Gate):∀ acc:List Stat × List Gate,
   k < acc.1.length->(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
   intro acc hk
   rw [k4,ih (qa n acc g) (by simp [qa];omega)]
   exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by
 cases o <;> simp
lemma q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil => intro acc h;exact h
 | cons g gs ih =>
   intro acc h
   apply ih (qa n acc g)
   intro g' hg'
   rcases List.mem_append.1 hg' with h1 | h1
   . exact h g' h1
   . exact q151 _ _ _ g' (by simpa using h1)
lemma q29 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).2.length<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (qa n acc g)
   have h2:(qa n acc g).2.length<=acc.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   rw [k4,lLC];omega
lemma zt (n k : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->k < acc.1.length->(∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) ->
   (∃ g ∈ gs,k ∈ g.inputs)->(elim n gs acc).2.length+1<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
   intro acc hok hk hc hex
   rw [k4,lLC]
   by_cases hkg:k ∈ g.inputs
   . obtain ⟨c,hc⟩:=hc
     have hnok:=hok g List.mem_cons_self
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hnok.1.1
       . simpa using hnok.1.2
       . intro h;simpa using hnok.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
     have h2:(qa n acc g).2.length=acc.2.length:=by
       show (acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
       rw [hnone];simp
     have:=q29 n gs (qa n acc g)
     omega
   . have hex':∃ g' ∈ gs,k ∈ g'.inputs:=by
       obtain ⟨g',hg',hk'⟩:=hex
       rcases List.mem_cons.1 hg' with rfl | h
       . exact absurd hk' hkg
       . exact ⟨g',h,hk'⟩
     have h1:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       (by simp [qa];omega)
       (by
         obtain ⟨c,hc⟩:=hc
         refine ⟨c,?_⟩
         simp only [qa]
         rw [q8 _ _ _ _ (by omega)];exact hc)
       hex'
     have h2:(qa n acc g).2.length<=acc.2.length+1:=by
       simp only [qa,lLA]
       have:=y2 (qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
       omega
     omega
lemma km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma jg (w t:List Bool):∀ s:Stat,qn w.length s ->
   ze (w++t) s=ze w s
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length/\∀ i : ℕ,
   qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
   ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
lemma j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=q3 acc.2 y with hw'
   have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw'];exact (hi a).1)
   rw [lw'] at hs
   set r:=qg g.op (n+acc.2.length) ins with hr
   have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,lMMp]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
     rw [zd]
   obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
   refine ⟨by simp [qa,hl],?_⟩
   intro i
   show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
     ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
   rw [hnew,lLA,← nAA]
   by_cases hil:i=acc.1.length
   . subst hil
     rw [z0,hl,z0]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
     refine ⟨km (by omega) _ (hi i).1,?_⟩
     rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
     exact (hi i).2
lemma q100 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,Ok g)->(∀ i,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) ->
   yq n acc.2->yq n (elim n gs acc).2:=by
 induction gs with
 | nil => intro acc _ _ hc;exact hc
 | cons g gs ih =>
   intro acc hok hv hc
   have hstep:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   apply hstep
   . intro i
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 (List.replicate (n+acc.2.length) false) ins
       (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         simpa using hv a)
     simp only [List.length_replicate] at hs
     show qn (n+(acc.2++_).length) ((acc.1++[_]).getD i (Sum.inl false))
     rw [lLA,← nAA]
     by_cases hil:i=acc.1.length
     . subst hil;rw [z0];exact hs.1
     . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
   . intro p g' hp
     simp only [qa] at hp
     by_cases hlt:p < acc.2.length
     . rw [List.getElem?_append_left hlt] at hp
       exact hc p g' hp
     . rw [List.getElem?_append_right (by omega)] at hp
       set r:=qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
       cases ho:r.1 with
       | none => simp [ho] at hp
       | some g0 =>
         rw [ho] at hp
         have hp0:p - acc.2.length=0:=by
           have:=(List.getElem?_eq_some_iff.1 hp).1
           simp at this;omega
         have hpeq:p=acc.2.length:=by omega
         rw [hp0] at hp
         simp at hp
         subst hp
         rw [hpeq]
         exact q80 g.op (n+acc.2.length) _ (by
           intro s hs
           obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
           exact hv a) g0 (by rw [← hr,ho];rfl)
def qd (n : ℕ) (b:Bool):List Stat :=
 List.ofFn (fun i:Fin n => Sum.inr (i : ℕ))++[Sum.inl b]
lemma kp (n : ℕ) (b:Bool) :
   (qd n b).getD n (Sum.inl false)=Sum.inl b :=
 z2 _ _ _ _ (by simp)
lemma q159 (n : ℕ) (b:Bool) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i
 have l1:(List.ofFn (fun i:Fin n => (Sum.inr (i : ℕ):Stat))).length=n:=by simp
 have l2:(List.ofFn y).length=n:=by simp
 by_cases hin:i=n
 . subst hin
   simp only [qd]
   rw [z2 _ _ _ _ l1,z2 _ _ _ _ l2]
   exact ⟨trivial,rfl⟩
 . simp only [qd]
   rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases hlt:i < n
   . simp [hlt,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
     exact ⟨trivial,rfl⟩
lemma q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
   List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
 rw [List.ofFn_succ']
 simp
lemma jr (n : ℕ) (gs:List Gate):∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,n ∉ g.inputs)->(∀ j : ℕ,j≠n->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q74 (m j : ℕ) (h:j < m) :
   (qr m).getD j ∅={⟨j,h⟩}:=by
 simp [qr,h]
lemma yi (n : ℕ):∀ j : ℕ,j≠n ->
   Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j hj
 by_cases hlt:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,hlt⟩}:=q74 (n+1) j hlt
   rw [e,Finset.mem_singleton]
   intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q115 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s',s'+1<=s/\HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 set acc:=elim n gs (qd n b,[]) with hacc
 have hinv:∀ y:Fin n->Bool,
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool))) acc:=by
   intro y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ y:Fin n->Bool,
     ze (q3 acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
       = f (Fin.snoc y b):=by
   intro y
   rw [((hinv y).2 C.output).2,hevg]
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst];rfl
 | inr j =>
   have hlen:acc.2.length+1<=s:=by
     by_cases hread:∃ g ∈ gs,n ∈ g.inputs
     . have:=zt n n gs (qd n b,[]) hnok (by simp [qd])
         ⟨b,z2 _ _ _ _ (by simp)⟩ hread
       rw [← hacc] at this
       have hl:gs.length=C.gates.length:=by simp [hgs]
       simp only [List.length_nil,zero_add] at this
       omega
     . exfalso
       push Not at hread
       have hout:C.output≠n:=by
         intro e
         rw [e,hacc,wy n n _ gs _ (by simp [qd])] at hst
         have hb:(qd n b).getD n (Sum.inl false)=Sum.inl b :=
           z2 _ _ _ _ (by simp)
         rw [show ((qd n b,([]:List Gate))).1=qd n b from rfl,hb] at hst
         cases hst
       obtain ⟨x,hx⟩:=hdep
       apply hx
       have hns:=jr n gs (qr (n+1)) hread (yi n) C.output hout
       have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
         (j4 _ _)).2.2 C.output (by
           intro k hk
           have:k≠Fin.last n:=fun e => hns (e ▸ hk)
           simp [fUN this])
       rw [← hevg,← hevg]
       exact hag
   refine ⟨acc.2.length,hlen,⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval y
   rw [hst] at this
   exact this
lemma q79 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (b:Bool)
   (hand:op=GateOp.and->b=false) (hor:op=GateOp.or->b=true)
   (hc:Sum.inl b ∈ ins):∃ c,(qg op m ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 . have:=hand rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ko]
 . have:=hor rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma vs (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (c:Bool) (hc:acc.1.getD k (Sum.inl false)=Sum.inl c) :
   (qa n acc g).2.length=acc.2.length:=by
 have hnone:(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
   apply jh
   . exact hg.1.1
   . simpa using hg.1.2
   . intro h;simpa using hg.2 h
   . exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
 show (acc.2++(qg g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
 rw [hnone];simp
def wl (g:Gate):Bool :=
 match g.op with
 | GateOp.or => true
 | _ => false
lemma q90 (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (hc:acc.1.getD k (Sum.inl false)=Sum.inl (wl g)) :
   ∃ c,(qa n acc g).1.getD acc.1.length (Sum.inl false)=Sum.inl c:=by
 have e:(qa n acc g).1.getD acc.1.length (Sum.inl false)
     = (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2:=z0 _ _ _
 rw [e]
 apply q79 _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
   (wl g)
 . intro h;simp [wl,h]
 . intro h;simp [wl,h]
 . exact List.mem_map.2 ⟨k,hk,hc⟩
lemma q53 {n : ℕ} (pre post:List Gate) (L:List (Finset (Fin n))) :
   zb (pre++post) L=zb post (zb pre L):=by
 simp [zb,List.foldl_append]
lemma q54 {n : ℕ} (gs:List Gate):∀ L:List (Finset (Fin n)),
   (zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil => intro L;rfl
 | cons g gs ih =>
   intro L
   have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl
   rw [h,ih]
   simp only [lLA,lLC,List.length_nil]
   omega
lemma q124 (n : ℕ) (D : ℕ->Prop) (gs:List Gate) :
   ∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,∀ a ∈ g.inputs,¬ D a)->(∀ j : ℕ,¬ D j->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,¬ D j->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (hno g List.mem_cons_self a ha) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q173 (n : ℕ) (gs:List Gate) (hnok:∀ g ∈ gs,NOk g) (o : ℕ)
   (hdep:Fin.last n ∈ (zb gs (qr (n+1))).getD o ∅)
   (hout:∀ b c,(elim n gs (qd n b,[])).1.getD o (Sum.inl false)≠Sum.inl c) :
   ∃ b,(elim n gs (qd n b,[])).2.length+2<=gs.length:=by
 have hon:o≠n:=by
   intro e
   apply hout false false
   rw [e,wy n n _ gs _ (by simp [qd])]
   exact kp n false
 by_cases hread:∃ g ∈ gs,n ∈ g.inputs
 swap
 . exfalso
   push Not at hread
   exact jr n gs (qr (n+1)) hread (yi n) o hon hdep
 obtain ⟨g,hg,hng⟩:=hread
 obtain ⟨pre,post,rfl⟩:=List.append_of_mem hg
 have hgn:NOk g:=hnok g hg
 have hpren:∀ g' ∈ pre,NOk g':=fun g' h => hnok g' (List.mem_append_left _ h)
 have hpostn:∀ g' ∈ post,NOk g' :=
   fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have hsplit:∀ b,elim n (pre++g::post) (qd n b,[])
     = elim n post (qa n (elim n pre (qd n b,[])) g) :=
   fun b => by rw [jz,k4]
 have hAn:∀ b,(elim n pre (qd n b,[])).1.getD n (Sum.inl false)=Sum.inl b:=by
   intro b
   rw [wy n n _ pre _ (by simp [qd])]
   exact kp n b
 have hAl:∀ b,(elim n pre (qd n b,[])).1.length=n+1+pre.length:=by
   intro b
   rw [q50]
   simp [qd]
 have hA2:∀ b,(elim n pre (qd n b,[])).2.length<=0+pre.length :=
   fun b => q29 n pre (qd n b,[])
 have hB2:=fun b => vs n (elim n pre (qd n b,[])) g hgn n hng b (hAn b)
 have hBl:∀ b,(qa n (elim n pre (qd n b,[])) g).1.length
     = n+1+pre.length+1:=by
   intro b
   simp [qa,hAl b]
 have hBn:∀ b,(qa n (elim n pre (qd n b,[])) g).1.getD n (Sum.inl false)
     = Sum.inl b:=by
   intro b
   show ((elim n pre (qd n b,[])).1++[_]).getD n _=_
   rw [q8 _ _ _ _ (by rw [hAl b];omega)]
   exact hAn b
 have hF:=fun b => q29 n post (qa n (elim n pre (qd n b,[])) g)
 have hlen:(pre++g::post).length=pre.length+post.length+1:=by
   simp only [lLA,lLC];omega
 by_cases h1:∃ g' ∈ pre,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:(elim n pre (qd n false,[])).2.length+1<=0+pre.length :=
     zt n n pre (qd n false,[]) hpren (by simp [qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 by_cases h2:∃ g' ∈ post,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:=zt n n post (qa n (elim n pre (qd n false,[])) g) hpostn
     (by rw [hBl];omega) ⟨false,hBn false⟩ h2
   have:=hA2 false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 obtain ⟨c,hc⟩:=q90 n (elim n pre (qd n (wl g),[])) g hgn n hng
   (hAn (wl g))
 rw [hAl (wl g)] at hc
 refine ⟨wl g,?_⟩
 by_cases h3:∃ g' ∈ post,(n+1+pre.length) ∈ g'.inputs
 . have a1:=zt n (n+1+pre.length) post
     (qa n (elim n pre (qd n (wl g),[])) g) hpostn
     (by rw [hBl];omega) ⟨c,hc⟩ h3
   have:=hA2 (wl g)
   have:=hB2 (wl g)
   rw [hsplit,hlen]
   omega
 . exfalso
   have hom:o≠n+1+pre.length:=by
     intro e
     apply hout (wl g) c
     rw [hsplit,e,wy n _ _ post _ (by rw [hBl];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (pre++g::post) (qr (n+1))
       = zb post (zb pre (qr (n+1))
         ++ [yb (zb pre (qr (n+1))) g]):=by
     rw [q53];rfl
   rw [hs] at hdep
   have hL:=jr n pre (qr (n+1)) h1 (yi n)
   have hLl:(zb pre (qr (n+1))).length=n+1+pre.length:=by
     rw [q54]
     simp [qr]
   refine q124 n (fun j => j=n\/j=n+1+pre.length) post _ ?_ ?_ o
     (by simp [hon,hom]) hdep
   . intro g' hg' a ha hD
     rcases hD with rfl | rfl
     . exact h2 g' hg' ha
     . exact h3 g' hg' ha
   . intro j hj
     have hj':j≠n/\j≠n+1+pre.length:=by
       constructor
       . exact fun e => hj (Or.inl e)
       . exact fun e => hj (Or.inr e)
     rw [q8 _ _ _ _ (by rw [hLl];exact hj'.2)]
     exact hL j hj'.1
lemma q114 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∀ b:Bool,∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hl:gs.length=C.gates.length:=by simp [hgs]
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 have hinv:∀ (b:Bool) (y:Fin n->Bool),
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)))
       (elim n gs (qd n b,[])):=by
   intro b y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ (b:Bool) (y:Fin n->Bool),
     ze (q3 (elim n gs (qd n b,[])).2 (List.ofFn y))
       ((elim n gs (qd n b,[])).1.getD C.output (Sum.inl false))=f (Fin.snoc y b):=by
   intro b y
   rw [((hinv b y).2 C.output).2,hevg]
 have hout:∀ b c,
     (elim n gs (qd n b,[])).1.getD C.output (Sum.inl false)≠Sum.inl c:=by
   intro b c hst
   obtain ⟨y,y',hne⟩:=hnc b
   apply hne
   rw [← hval b y,← hval b y',hst];rfl
 have hsupp:Fin.last n ∈ (zb gs (qr (n+1))).getD C.output ∅:=by
   by_contra hns
   obtain ⟨x,hx⟩:=hdep
   apply hx
   have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠Fin.last n:=fun e => hns (e ▸ hk)
       simp [fUN this])
   rw [← hevg,← hevg]
   exact hag
 obtain ⟨b,hb⟩:=q173 n gs hnok C.output hsupp hout
 cases hst:(elim n gs (qd n b,[])).1.getD C.output (Sum.inl false) with
 | inl c => exact absurd hst (hout b c)
 | inr j =>
   refine ⟨b,(elim n gs (qd n b,[])).2.length,by omega,
     ⟨(elim n gs (qd n b,[])).2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval b y
   rw [hst] at this
   exact this
def wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
 if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
def jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
 ⟨C.gates.map (jt n m π),wmap n m π C.output⟩
def step (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
 n<=W.length/\W'.length+n=W.length+m /\
   ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
lemma q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
   (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv:(jt n m π g).op.eval
     ((jt n m π g).inputs.map fun i => W'.getD i false)
     = g.op.eval (g.inputs.map fun i => W.getD i false):=by
   simp only [jt,lMMp]
   congr 1
   apply List.map_congr_left
   intro a _
   exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w
 simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 . have hlt:wmap n m π w < W'.length:=by
     unfold wmap
     split
     . have:=(π ⟨w,by assumption⟩).2;omega
     . omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
   exact h3 w
 . have he:wmap n m π w=W'.length:=by
     unfold wmap
     split
     . omega
     . omega
   rw [he,hw,z0,z0]
 . have hge:W'.length+1<=wmap n m π w:=by
     unfold wmap
     split
     . omega
     . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
lemma q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
   ∀ W W':List Bool,Rel n m π W W' ->
     Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   exact ih _ _ (q182 n m π W W' g h)
lemma q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
   Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w
 unfold wmap
 split
 . rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 . rename_i hw
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
lemma yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
   (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨q174 n m π C,?_,?_,?_⟩
 . intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
 . simpa [q174,Circuit.size] using hsz
 . intro x
   show _=h (x ∘ π)
   rw [← hev (x ∘ π)]
   have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
   exact this
lemma ks (n : ℕ) (p:Fin (n+1)) (x:Fin (n+1)->Bool) (b:Bool) :
   (Fin.snoc (fun j:Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
       Fin (n+1)->Bool) ∘ (Equiv.swap p (Fin.last n))
     = Function.update x p b:=by
 funext j
 simp only [Function.comp_apply]
 by_cases hj:j=p
 . subst hj
   rw [Equiv.swap_apply_left,Fin.snoc_last,fUS]
 . have hl:Equiv.swap p (Fin.last n) j≠Fin.last n:=by
     intro e
     apply hj
     have:=congrArg (Equiv.swap p (Fin.last n)) e
     rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain ⟨t,ht⟩:=Fin.exists_castSucc_eq.2 hl
   rw [← ht,Fin.snoc_castSucc,ht,Equiv.swap_apply_self,fUN hj]
lemma q70 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s' : ℕ,s'+1<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   obtain ⟨x,y,hxy⟩:=hnc
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨s',hs,h'⟩:=q115 n _ b s hdep' hnc' hg
 refine ⟨s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
lemma q141 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∀ b:Bool,∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∀ b:Bool,∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   intro b
   obtain ⟨x,y,hxy⟩:=hnc b
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨b,s',hs,h'⟩:=q114 n _ s hdep' hnc' hg
 refine ⟨b,s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
def val (gs:List Gate) (n : ℕ) (a : ℕ):BFn n :=
 fun x => (q3 gs (List.ofFn x)).getD a false
lemma q172 (gs:List Gate) (n : ℕ) (i:Fin n):val gs n i=fun x => x i:=by
 funext x
 unfold val
 rw [ve _ _ _ (by simp)]
 simp
lemma q60 {α:Type} (gs:List α) (p : ℕ) (g : α) (hp:gs[p]?=some g) :
   ∃ pre post,gs=pre++g::post/\pre.length=p:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hp).1
 have hget:gs[p]=g:=(List.getElem?_eq_some_iff.1 hp).2
 refine ⟨gs.take p,gs.drop (p+1),?_,by simp;omega⟩
 have h1:gs=gs.take p++gs.drop p:=(List.take_append_drop p gs).symm
 have h2:gs.drop p=gs[p]::gs.drop (p+1):=List.drop_eq_getElem_cons hlt
 exact h1.trans (by rw [h2,hget])
lemma q103 (n : ℕ) (gs:List Gate) (p : ℕ) (g:Gate) (hp:gs[p]?=some g)
   (hlt:∀ a ∈ g.inputs,a < n+p) (x:Fin n->Bool) :
   val gs n (n+p) x=g.op.eval (g.inputs.map fun a => val gs n a x):=by
 obtain ⟨pre,post,rfl,hlen⟩:=q60 gs p g hp
 unfold val
 have h1:q3 (pre++g::post) (List.ofFn x)=q3 post
     (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]):=by
   rw [zd];rfl
 have hl:(q3 pre (List.ofFn x)).length=n+p:=by
   rw [qu];simp [hlen]
 rw [h1,ve _ _ _ (by simp [hl]),z2 _ _ _ _ hl]
 congr 1
 apply List.map_congr_left
 intro a ha
 have hal:=hlt a ha
 have e1:=ve post (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]) a
       (by simp [hl];omega)
 rw [e1,List.getD_append _ _ _ _ (by omega)]
def vi (n : ℕ):List Stat:=List.ofFn fun i:Fin n => Sum.inr (i : ℕ)
lemma q165 (n : ℕ) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y) (vi n,[]):=by
 refine ⟨by simp [vi],?_⟩
 intro i
 by_cases hlt:i < n
 . simp [vi,hlt,qn,ze,q3]
 . rw [lGD _ _ (by simp [vi];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma q48 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,yq n gs/\gs.length<=s/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set acc:=elim n C.gates (vi n,[]) with hacc
 have hinv:∀ y:Fin n->Bool,Inv n (List.ofFn y) (q3 C.gates (List.ofFn y)) acc :=
   fun y => j7 n _ (by simp) C.gates _ _ ok (q165 n y)
 have hcl:yq n acc.2:=by
   apply q100 n C.gates (vi n,[]) ok
   . intro i
     by_cases hlt:i < n
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
   . intro p g hp;simp at hp
 have hlen:acc.2.length<=s:=by
   have:=q29 n C.gates (vi n,[])
   rw [← hacc] at this
   simp only [List.length_nil,zero_add] at this
   omega
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=((hinv y).2 C.output).2
   have e2:=((hinv y').2 C.output).2
   rw [hst] at e1 e2
   have h1:(q3 C.gates (List.ofFn y)).getD C.output false=f y:=hev y
   have h2:(q3 C.gates (List.ofFn y')).getD C.output false=f y':=hev y'
   rw [← h1,← h2,← e1,← e2];rfl
 | inr j =>
   have hj:j < n+acc.2.length:=by
     obtain ⟨y,_,_⟩:=hnc
     have:=((hinv y).2 C.output).1
     rw [hst] at this
     exact this
   refine ⟨acc.2,j,hcl,hlen,hj,?_⟩
   intro x
   have e1:=((hinv x).2 C.output).2
   rw [hst] at e1
   exact e1.trans (hev x)
def qk {α:Type} (b:Bool) (x : α) (xs:List α):List α :=
 if b then x::xs else xs
def Run {α:Type} (inv : α->α) (meet join : α->α->α) (y : α) (t : ℕ) (ws:List α):Prop :=
 ∀ P : ℕ->List α->Prop,P 0 [y] ->
   (∀ {s xs zs},List.Perm xs zs->P s xs->P s zs) ->
   (∀ {s a r} (neg save:Bool),P s ((if neg then inv a else a)::qk save a r) ->
     P (s+1) (a::r)) ->
   (∀ {s a b r} (c ka kb:Bool),
     P s ((if c then meet a b else join a b)::qk ka a (qk kb b r)) ->
     P (s+1) (a::b::r))->P t ws
lemma Run.done {α inv meet join y} : @Run α inv meet join y 0 [y]:=fun _ d _ _ _ => d
lemma Run.perm {α inv meet join y s xs zs} (p:List.Perm xs zs)
   (h : @Run α inv meet join y s xs):Run inv meet join y s zs :=
 fun P d q u b => q p (h P d q u b)
lemma Run.one {α inv meet join y s a r} (neg save:Bool)
   (h : @Run α inv meet join y s ((if neg then inv a else a)::qk save a r)) :
   Run inv meet join y (s+1) (a::r):=fun P d q u b => u neg save (h P d q u b)
lemma Run.two {α inv meet join y s a b r} (c ka kb:Bool)
   (h : @Run α inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))) :
   Run inv meet join y (s+1) (a::b::r):=fun P d q u v => v c ka kb (h P d q u v)
lemma Run.fold {α inv meet join y} {P:∀ t ws,@Run α inv meet join y t ws->Prop}
   (done:P 0 [y] Run.done)
   (perm:∀ {s xs zs} (hp:List.Perm xs zs) (h:Run inv meet join y s xs),
     P s xs h->P s zs (Run.perm hp h))
   (one:∀ {s a r} (neg save:Bool)
     (h:Run inv meet join y s ((if neg then inv a else a)::qk save a r)),
     P _ _ h->P _ _ (Run.one neg save h))
   (two:∀ {s a b r} (c ka kb:Bool)
     (h:Run inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))),
     P _ _ h->P _ _ (Run.two c ka kb h))
   {t ws} (h:Run inv meet join y t ws):P t ws h:=by
 have hex:=h (fun s xs => ∃ h':Run inv meet join y s xs,P s xs h')
   ⟨Run.done,done⟩
   (fun hp ⟨h',ih⟩ => ⟨Run.perm hp h',perm hp h' ih⟩)
   (fun n k ⟨h',ih⟩ => ⟨Run.one n k h',one n k h' ih⟩)
   (fun c a b ⟨h',ih⟩ => ⟨Run.two c a b h',two c a b h' ih⟩)
 exact hex.elim fun _ hp => hp
lemma wd {α β:Type} (e : α->β) (b:Bool) (x : α) (xs:List α) :
   (qk b x xs).map e=qk b (e x) (xs.map e):=by cases b <;> simp [qk]
lemma wa {α:Type} (b:Bool) (x a : α) (xs:List α) :
   a ∈ qk b x xs ↔ (b=true/\a=x)\/a ∈ xs:=by cases b <;> simp [qk]
lemma q36 {α:Type} (b:Bool) (x : α) (xs:List α) (h:xs.Nodup) (hx:x ∉ xs) :
   (qk b x xs).Nodup:=by
 cases b
 . simpa [qk] using h
 . simpa [qk] using And.intro hx h
lemma Run.map {α β:Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
   {inv' : β->β} {meet' join' : β->β->β}
   (hi:∀ a,e (inv a)=inv' (e a)) (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {y : α} {s : ℕ} {ws:List α} (h:Run inv meet join y s ws) :
   Run inv' meet' join' (e y) s (ws.map e):=by
 induction h using Run.fold with
 | done => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map e) ih
 | @one s a rest neg save _ ih =>
   have e1:((if neg then inv a else a)::qk save a rest).map e
       = (if neg then inv' (e a) else e a)::qk save (e a) (rest.map e):=by
     cases neg <;> simp [wd,hi]
   rw [e1] at ih
   exact Run.one neg save ih
 | @two s a b rest conj ka kb _ ih =>
   have e1:((if conj then meet a b else join a b)::qk ka a (qk kb b rest)).map e
       = (if conj then meet' (e a) (e b) else join' (e a) (e b))
           :: qk ka (e a) (qk kb (e b) (rest.map e)):=by
     cases conj <;> simp [wd,hm,hj]
   rw [e1] at ih
   exact Run.two conj ka kb ih
def wn (n : ℕ) (gs:List Gate) (o a : ℕ):Prop :=
 ∀ P : ℕ->Prop,P o ->
   (∀ q g,gs[q]?=some g->P (n+q)->∀ u ∈ g.inputs,P u)->P a
lemma q34 (n : ℕ) (gs:List Gate) (o : ℕ):wn n gs o o :=
 fun _ ho _ => ho
lemma q33 {n : ℕ} {gs:List Gate} {o q u : ℕ} {g:Gate}
   (hq:gs[q]?=some g) (hr:wn n gs o (n+q)) (hu:u ∈ g.inputs) :
   wn n gs o u :=
 fun P ho hs => hs q g hq (hr P ho hs) u hu
lemma q66 {n : ℕ} {gs:List Gate} {o a : ℕ} (h:wn n gs o a) :
   a=o\/∃ q g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q):=by
 apply h (fun x => x=o\/∃ q g,gs[q]?=some g/\x ∈ g.inputs/\wn n gs o (n+q))
 . exact Or.inl rfl
 . intro q g hq hP u hu
   refine Or.inr ⟨q,g,hq,hu,?_⟩
   rcases hP with rfl | ⟨q',g',hq',hin',hr'⟩
   . exact q34 n gs (n+q)
   . exact q33 hq' hr' hin'
def q11 (n : ℕ) (gs:List Gate) (o p a : ℕ):Prop :=
 a=o\/∃ q,p<=q/\∃ g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q)
open Classical in
noncomputable def liveList (gs:List Gate) (n o p : ℕ):List ℕ :=
 (List.range (n+p)).filter (fun a => decide (q11 n gs o p a))
lemma qw (gs:List Gate) (n o p a : ℕ) :
   a ∈ liveList gs n o p ↔ a < n+p/\q11 n gs o p a:=by
 simp [liveList]
lemma vy (gs:List Gate) (n o p : ℕ):(liveList gs n o p).Nodup :=
 List.Nodup.filter _ List.nodup_range
abbrev invF {n : ℕ}:BFn n->BFn n:=fun a x => !a x
abbrev meetF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x&&b x
abbrev joinF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x||b x
lemma q73 (n : ℕ) (gs:List Gate) (o : ℕ) (hcl:yq n gs)
   (p : ℕ) (g:Gate) (hg:gs[p]?=some g) (hr:wn n gs o (n+p)) (a : ℕ) :
   a ∈ liveList gs n o (p+1) ↔
     a=n+p\/(a ∈ liveList gs n o p/\(a ∈ g.inputs->q11 n gs o (p+1) a)):=by
 rw [qw,qw]
 constructor
 . rintro ⟨hlt,hl⟩
   by_cases ha:a=n+p
   . exact Or.inl ha
   . refine Or.inr ⟨⟨by omega,?_⟩,fun _ => hl⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
 . rintro (rfl | ⟨⟨hlt,hl⟩,himp⟩)
   . refine ⟨by omega,?_⟩
     rcases q66 hr with h | ⟨q,g',hg',hin,hrq⟩
     . exact Or.inl h
     . refine Or.inr ⟨q,?_,g',hg',hin,hrq⟩
       have:=j2 (hcl q g' hg') _ hin
       omega
   . refine ⟨by omega,?_⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . by_cases hqp:q=p
       . subst hqp
         rw [hg] at hg'
         cases hg'
         exact himp hin
       . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
def gfn {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)):BFn n :=
 fun x => A.any (fun a => x a)||E.any (fun e => x e.1&&x e.2)
def j9 {α:Type} [BEq α]:List α->List α->List α
 | [],acc => acc.reverse
 | a::t,acc => if acc.contains a then j9 t acc else j9 t (a::acc)
def q206 {α:Type} [BEq α] (l:List α):List α:=j9 l []
lemma ww {α:Type} [DecidableEq α]:∀ (l acc:List α) (x : α),
   x ∈ j9 l acc ↔ x ∈ l\/x ∈ acc
 | [],acc,x => by simp [j9]
 | a::t,acc,x => by
   simp only [j9]
   by_cases h:acc.contains a=true
   . simp only [h,↓reduceIte,ww,lMM]
     have ha:a ∈ acc:=by simpa using h
     constructor
     . rintro (ht | hacc)
       . exact Or.inl (Or.inr ht)
       . exact Or.inr hacc
     . rintro ((rfl | ht) | hacc)
       . exact Or.inr ha
       . exact Or.inl ht
       . exact Or.inr hacc
   . simp only [h,bFT,↓reduceIte,ww,lMM]
     tauto
lemma q23 {α:Type} [DecidableEq α] (l:List α) (x : α) :
   x ∈ q206 l ↔ x ∈ l:=by
 simpa [q206] using ww l [] x
def fix0A {n : ℕ} (A:List (Fin n)) (p:Fin n):List (Fin n) :=
 A.filter (·!=p)
def fix0E {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 E.filter (fun e => e.1!=p&&e.2!=p)
def nbrs {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 E.filterMap (fun e => if e.1==p then some e.2 else if e.2==p then some e.1 else none)
def fix1A {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 q206 (A++nbrs E p)
def fix1E {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 let A1:=fix1A A E p
 E.filter (fun e => e.1!=p&&e.2!=p&&!A1.contains e.1&&!A1.contains e.2)
def depCheck {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):Bool :=
 A.contains p ||
   (E.all (fun e => e.1!=e.2) &&
     E.any (fun e => (e.1==p&&!A.contains e.2)||(e.2==p&&!A.contains e.1)))
def isoCheck {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k)) (π:Fin n->Fin k):Bool :=
 E.all (fun e => Eb.any (fun e' => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1))) &&
 Eb.all (fun e' => E.any (fun e => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1)))
lemma q216 {n val1 val2 : ℕ} {f:BFn n} (hle:val1<=val2)
   (h:∀ s,HasCircuitSize n f s->val2<=s):∀ s,HasCircuitSize n f s->val1<=s :=
 fun s hs => le_trans hle (h s hs)
lemma q176 {n : ℕ} (A:List (Fin n)) (hnd:A.Nodup) :
   ∀ s : ℕ,HasCircuitSize n (gfn A []) s->A.length - 1<=s:=by
 intro s h
 have hd:=q117 n (gfn A []) A.toFinset (by
   intro i hi
   have hiA:i ∈ A:=List.mem_toFinset.1 hi
   refine ⟨fun _ => false,?_⟩
   have h0:gfn A [] (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A [] (Function.update (fun _ => false) i true)=true:=by
     simp only [gfn,List.any_nil,Bool.or_false,lAN]
     exact ⟨i,hiA,by simp⟩
   simpa [h0,h1]) s h
 rw [List.toFinset_card_of_nodup hnd] at hd
 omega
lemma q99 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n))
   (h:(!A.isEmpty||!E.isEmpty)=true) :
   ∃ x y:Fin n->Bool,gfn A E x≠gfn A E y:=by
 refine ⟨fun _ => false,fun _ => true,?_⟩
 have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
 have h1:gfn A E (fun _ => true)=true:=by
   cases A with
   | cons a t => simp [gfn]
   | nil =>
     cases E with
     | nil => simp at h
     | cons e t => simp [gfn]
 rw [h0,h1];decide
lemma q154 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (h:depCheck A E p=true) :
   ∃ x:Fin n->Bool,gfn A E (Function.update x p (!x p))≠gfn A E x:=by
 simp only [depCheck,bOT,bAT,List.contains_eq_mem,decide_eq_true_eq,
   lAL,lAN,bne_iff_ne,beq_iff_eq,bNT,
   decide_eq_false_iff_not] at h
 rcases h with hpA | ⟨hloop,⟨e,heE,⟨rfl,hqA⟩ | ⟨rfl,hqA⟩⟩⟩
 . refine ⟨fun _ => false,?_⟩
   have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A E (Function.update (fun _ => false) p true)=true:=by
     simp only [gfn,bOT,lAN]
     exact Or.inl ⟨p,hpA,by simp⟩
   simpa [h0,h1]
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.2),?_⟩
   have h0:gfn A E (fun i => decide (i=e.2))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.2)) e.1 (!decide (e.1=e.2)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [hne]
     . simp [fUN (Ne.symm hne)]
   rw [h0,h1];decide
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.1),?_⟩
   have h0:gfn A E (fun i => decide (i=e.1))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.1)) e.2 (!decide (e.2=e.1)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [fUN hne]
     . simp [Ne.symm hne]
   rw [h0,h1];decide
lemma zo {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n) :
   (fun x => gfn A E (Function.update x p false))=gfn (fix0A A p) (fix0E E p):=by
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix0A,fix0E,bOT,lAN,List.mem_filter,
   bAT,bne_iff_ne]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . by_cases hap:a=p
     . subst hap;simp at hxa
     . exact Or.inl ⟨a,⟨ha,hap⟩,by simpa [fUN hap] using hxa⟩
   . by_cases h1p:e.1=p
     . rw [h1p,fUS] at h1;cases h1
     . by_cases h2p:e.2=p
       . rw [h2p,fUS] at h2;cases h2
       . exact Or.inr ⟨e,⟨he,h1p,h2p⟩,
           by simpa [fUN h1p] using h1,
           by simpa [fUN h2p] using h2⟩
 . rintro (⟨a,⟨ha,hap⟩,hxa⟩ | ⟨e,⟨he,h1p,h2p⟩,h1,h2⟩)
   . exact Or.inl ⟨a,ha,by simpa [fUN hap] using hxa⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using h1,
       by simpa [fUN h2p] using h2⟩
lemma q109 {n : ℕ} (E:List (Fin n × Fin n)) (p q:Fin n) :
   q ∈ nbrs E p ↔ ∃ e ∈ E,(e.1=p/\e.2=q)\/(e.1≠p/\e.2=p/\e.1=q):=by
 simp only [nbrs,List.mem_filterMap,beq_iff_eq]
 constructor
 . rintro ⟨e,he,h⟩
   split_ifs at h with h1 h2
   . cases h;exact ⟨e,he,Or.inl ⟨h1,rfl⟩⟩
   . cases h;exact ⟨e,he,Or.inr ⟨h1,h2,rfl⟩⟩
 . rintro ⟨e,he,⟨h1,h2⟩ | ⟨h1,h2,h3⟩⟩
   . exact ⟨e,he,by rw [if_pos h1,h2]⟩
   . exact ⟨e,he,by rw [if_neg h1,if_pos h2,h3]⟩
lemma kx {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true) :
   (fun x => gfn A E (Function.update x p true))=gfn (fix1A A E p) (fix1E A E p):=by
 have hpnot:p ∉ A:=by simpa [List.contains_eq_mem] using hpA
 have hne:∀ e ∈ E,e.1≠e.2:=by simpa [lAL,bne_iff_ne] using hloop
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix1E,bOT,lAN,bAT,List.mem_filter,
   bne_iff_ne,bNT,List.contains_eq_mem,decide_eq_false_iff_not]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . have hap:a≠p:=fun h => hpnot (h ▸ ha)
     refine Or.inl ⟨a,?_,by simpa [fUN hap] using hxa⟩
     rw [fix1A,q23];exact List.mem_append_left _ ha
   . by_cases h1p:e.1=p
     . have h2p:e.2≠p:=fun h => hne e he (h1p.trans h.symm)
       refine Or.inl ⟨e.2,?_,by simpa [fUN h2p] using h2⟩
       rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.2).2 ⟨e,he,Or.inl ⟨h1p,rfl⟩⟩)
     . by_cases h2p:e.2=p
       . refine Or.inl ⟨e.1,?_,by simpa [fUN h1p] using h1⟩
         rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.1).2 ⟨e,he,Or.inr ⟨h1p,h2p,rfl⟩⟩)
       . have hx1:x e.1=true:=by simpa [fUN h1p] using h1
         have hx2:x e.2=true:=by simpa [fUN h2p] using h2
         by_cases m1:e.1 ∈ fix1A A E p
         . exact Or.inl ⟨e.1,m1,hx1⟩
         . by_cases m2:e.2 ∈ fix1A A E p
           . exact Or.inl ⟨e.2,m2,hx2⟩
           . exact Or.inr ⟨e,⟨he,⟨⟨h1p,h2p⟩,m1⟩,m2⟩,hx1,hx2⟩
 . rintro (⟨a,ha,hxa⟩ | ⟨e,⟨he,⟨⟨h1p,h2p⟩,_⟩,_⟩,hx1,hx2⟩)
   . rw [fix1A,q23,List.mem_append] at ha
     rcases ha with haA | han
     . have hap:a≠p:=fun h => hpnot (h ▸ haA)
       exact Or.inl ⟨a,haA,by simpa [fUN hap] using hxa⟩
     . obtain ⟨e,he,⟨h1,rfl⟩ | ⟨h1,h2,rfl⟩⟩:=(q109 E p a).1 han
       . have h2p:e.2≠p:=fun h => hne e he (h1.trans h.symm)
         exact Or.inr ⟨e,he,by simp [h1],by simpa [fUN h2p] using hxa⟩
       . exact Or.inr ⟨e,he,by simpa [fUN h1] using hxa,by simp [h2]⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using hx1,
       by simpa [fUN h2p] using hx2⟩
lemma q190 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hA:A'=fix0A A p) (hE:E'=fix0E E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p false))=gfn A' E':=by
   rw [hA,hE];exact zo A E p
 have hnc':∃ x y,gfn A E (Function.update x p false)≠gfn A E (Function.update y p false):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p false s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega
lemma q189 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA:A'=fix1A A E p) (hE:E'=fix1E A E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p true))=gfn A' E':=by
   rw [hA,hE];exact kx A E p hpA hloop
 have hnc':∃ x y,gfn A E (Function.update x p true)≠gfn A E (Function.update y p true):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p true s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega
lemma q155 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1))
   (A0:List (Fin (n+1))) (E0:List (Fin (n+1) × Fin (n+1)))
   (A1:List (Fin (n+1))) (E1:List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA0:A0=fix0A A p) (hE0:E0=fix0E E p)
   (hA1:A1=fix1A A E p) (hE1:E1=fix1E A E p)
   (hnc0:(!A0.isEmpty||!E0.isEmpty)=true)
   (hnc1:(!A1.isEmpty||!E1.isEmpty)=true)
   (ih0:∀ s,HasCircuitSize (n+1) (gfn A0 E0) s->k<=s)
   (ih1:∀ s,HasCircuitSize (n+1) (gfn A1 E1) s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+2<=s:=by
 intro s h
 have hres0:(fun x => gfn A E (Function.update x p false))=gfn A0 E0:=by
   rw [hA0,hE0];exact zo A E p
 have hres1:(fun x => gfn A E (Function.update x p true))=gfn A1 E1:=by
   rw [hA1,hE1];exact kx A E p hpA hloop
 have hnc:∀ b:Bool,∃ x y,gfn A E (Function.update x p b)≠gfn A E (Function.update y p b):=by
   intro b
   cases b with
   | false =>
     obtain ⟨x,y,hxy⟩:=q99 A0 E0 hnc0
     exact ⟨x,y,by simpa [congrFun hres0] using hxy⟩
   | true =>
     obtain ⟨x,y,hxy⟩:=q99 A1 E1 hnc1
     exact ⟨x,y,by simpa [congrFun hres1] using hxy⟩
 obtain ⟨b,s',hs',h'⟩:=q141 n (gfn A E) p s (q154 A E p hdep) hnc h
 cases b with
 | false => rw [hres0] at h';have:=ih0 s' h';omega
 | true => rw [hres1] at h';have:=ih1 s' h';omega
lemma q204 {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true) :
   (fun y:Fin k->Bool => gfn [] E (y ∘ π))=gfn [] Eb:=by
 simp only [isoCheck,bAT,lAL,lAN,
   bOT,beq_iff_eq] at hiso
 obtain ⟨h1,h2⟩:=hiso
 funext y
 apply Bool.eq_iff_iff.2
 simp only [gfn,List.any_nil,Bool.false_or,lAN,bAT,Function.comp_apply]
 constructor
 . rintro ⟨e,he,hy1,hy2⟩
   obtain ⟨e',he',⟨a,b⟩ | ⟨a,b⟩⟩:=h1 e he
   . exact ⟨e',he',a ▸ hy1,b ▸ hy2⟩
   . exact ⟨e',he',b ▸ hy2,a ▸ hy1⟩
 . rintro ⟨e',he',hy1,hy2⟩
   obtain ⟨e,he,⟨a,b⟩ | ⟨a,b⟩⟩:=h2 e' he'
   . exact ⟨e,he,a.symm ▸ hy1,b.symm ▸ hy2⟩
   . exact ⟨e,he,a.symm ▸ hy2,b.symm ▸ hy1⟩
lemma q191 {n k val : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true)
   (hb:∀ s : ℕ,HasCircuitSize k (gfn [] Eb) s->val<=s) :
   ∀ s : ℕ,HasCircuitSize n (gfn [] E) s->val<=s:=by
 intro s h
 have h':=yn π (gfn [] E) s h
 rw [q204 E Eb π hiso] at h'
 exact hb s h'
lemma q202 {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
   xs.length<=s+1:=by
 induction h using Run.fold with
 | done => simp
 | perm hp _ ih => rwa [← hp.length_eq]
 | one neg save h ih => cases save <;> simp_all [qk] <;> omega
 | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [qk] <;> omega
lemma q101 {m : ℕ} {g:Gate} (h:q161 m g):NOk g:=by
 rcases h with ⟨hop,j,_,hin⟩ | ⟨hop,j,k,_,_,hin⟩
 . exact ⟨⟨by simp [hop],by simp [hin]⟩,fun _ => by simp [hin]⟩
 . refine ⟨⟨?_,by simp [hin]⟩,fun hnot => ?_⟩
   . rcases hop with h1 | h1 <;> simp [h1]
   . rcases hop with h1 | h1 <;> rw [h1] at hnot <;> cases hnot
lemma ja {n : ℕ} {gs:List Gate} (h:yq n gs):∀ g ∈ gs,NOk g:=by
 intro g hg
 obtain ⟨p,hp,rfl⟩:=List.getElem_of_mem hg
 exact q101 (h p gs[p] (List.getElem?_eq_getElem hp))
lemma q157 {n : ℕ} {gs:List Gate} (h:yq n gs) (p : ℕ):yq n (gs.take p):=by
 intro q g hq
 have hlt:q < (gs.take p).length:=(List.getElem?_eq_some_iff.1 hq).1
 have hqp:q < p:=by simp at hlt;omega
 rw [List.getElem?_take_of_lt hqp] at hq
 exact h q g hq
def InvR (R : ℕ->Prop) (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length /\
 (∀ i : ℕ,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) /\
 (∀ i : ℕ,R i->ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false)
lemma q175 (R : ℕ->Prop) (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g) ->
     (∀ q g,gs[q]?=some g->R (acc.1.length+q)->∀ a ∈ g.inputs,R a) ->
     InvR R n y w acc ->
     InvR R n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ _ h;exact h
 | cons g gs ih =>
   intro w acc hok hR h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   . intro q g' hq hRq a ha
     have hlen:(qa n acc g).1.length=acc.1.length+1:=by simp [qa]
     rw [hlen] at hRq
     exact hR (q+1) g' (by simpa using hq) (by simpa [nAA,nAC 1 q] using hRq) a ha
   . obtain ⟨hl,hv,he⟩:=h
     set w':=q3 acc.2 y with hw'
     have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         rw [lw'];exact hv a)
     rw [lw'] at hs
     set r:=qg g.op (n+acc.2.length) ins with hr
     have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
       rw [zd]
     obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
     refine ⟨by simp [qa,hl],?_,?_⟩
     . intro i
       show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false))
       rw [lLA,← nAA]
       by_cases hil:i=acc.1.length
       . subst hil;rw [z0];exact hs.1
       . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
     . intro i hi
       show ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
       rw [hnew]
       by_cases hil:i=acc.1.length
       . subst hil
         rw [z0,hl,z0,hs.2]
         congr 1
         rw [hins,lMMp]
         apply List.map_congr_left
         intro a ha
         exact he a (hR 0 g rfl (by simpa using hi) a ha)
       . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
         rw [ht,jg _ _ _ (by rw [lw'];exact hv i)]
         exact he i hi
lemma y7 (n : ℕ) (f:BFn n) (pre post:List Gate) (g:Gate) (o : ℕ)
   (hcl:yq n (pre++g::post)) (ho:o < n+(pre++g::post).length)
   (hev:∀ x,val (pre++g::post) n o x=f x)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (st:Stat) (hstV:qn (n+pre.length) st)
   (hcond:(∀ x,ze (q3 pre (List.ofFn x)) st=val (pre++g::post) n (n+pre.length) x) \/
            ¬ wn n (pre++g::post) o (n+pre.length)) :
   ∃ gs' o',yq n gs'/\gs'.length<=pre.length+post.length /\
     o' < n+gs'.length/\∀ x,val gs' n o' x=f x:=by
 set gs:=pre++g::post with hgs
 set p:=pre.length with hp
 set acc0:List Stat × List Gate:=(vi (n+p)++[st],pre) with hacc0
 set acc:=elim n post acc0 with hacc
 have hok_post:∀ g' ∈ post,Ok g':=fun g' hg' =>
   (ja hcl g' (List.mem_append_right _ (List.mem_cons_of_mem _ hg'))).1
 have hcl_pre:yq n pre:=by
   have:pre=gs.take p:=by simp [hgs,hp]
   rw [this];exact q157 hcl p
 have hv0:∀ i,qn (n+acc0.2.length) (acc0.1.getD i (Sum.inl false)):=by
   intro i
   simp only [hacc0,hp]
   by_cases hip:i=n+pre.length
   . subst hip;rw [z2 _ _ _ _ (by simp [vi])];exact hstV
   . rw [q8 _ _ _ _ (by simp [vi];omega)]
     by_cases hlt:i < n+pre.length
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
 have hcl':yq n acc.2:=q100 n post acc0 hok_post hv0 hcl_pre
 have hlen':acc.2.length<=pre.length+post.length:=by
   simpa [hacc,hacc0] using q29 n post acc0
 have hinv_all:∀ x:Fin n->Bool,
     qn (n+acc.2.length) (acc.1.getD o (Sum.inl false)) /\
     ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))=f x:=by
   intro x
   have hsplit:q3 gs (List.ofFn x)=q3 post (q3 (pre++[g]) (List.ofFn x)):=by
     have:gs=(pre++[g])++post:=by simp [hgs]
     rw [this,zd]
   have hl1:(q3 (pre++[g]) (List.ofFn x)).length=n+p+1:=by
     rw [qu];simp [hp];omega
   have hval_lt:∀ i < n+p,(q3 (pre++[g]) (List.ofFn x)).getD i false =
       (q3 pre (List.ofFn x)).getD i false:=by
     intro i hi
     rw [zd,ve _ _ _ (by rw [qu];simp;omega)]
   rcases hcond with hval_eq | hdead
   . have hinv0:Inv n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],?_⟩
       intro i
       refine ⟨hv0 i,?_⟩
       simp only [hacc0]
       by_cases hip:i=n+p
       . subst hip
         rw [z2 _ _ _ _ (by simp [vi])]
         have h1:=hval_eq x
         unfold val at h1
         rw [hsplit,ve _ _ _ (by omega)] at h1
         exact h1
       . rw [q8 _ _ _ _ (by simp [vi];omega)]
         by_cases hlt:i < n+p
         . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
             Option.getD_some,ze]
           exact (hval_lt i hlt).symm
         . rw [lGD _ _ (by simp [vi];omega),
               lGD _ _ (by omega)];rfl
     have hres:=j7 n (List.ofFn x) (by simp) post _ acc0 hok_post hinv0
     rw [← hsplit] at hres
     have h1:=hres.2 o
     exact ⟨h1.1,h1.2.trans (hev x)⟩
   . have hinv0:InvR (wn n gs o) n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],hv0,?_⟩
       intro i hi
       simp only [hacc0]
       have hne:i≠n+p:=fun e => hdead (e ▸ hi)
       rw [q8 _ _ _ _ (by simp [vi];omega)]
       by_cases hlt:i < n+p
       . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
           Option.getD_some,ze]
         exact (hval_lt i hlt).symm
       . rw [lGD _ _ (by simp [vi];omega),
             lGD _ _ (by omega)];rfl
     have hR:∀ q g',post[q]?=some g'->wn n gs o (acc0.1.length+q)->∀ a ∈ g'.inputs,wn n gs o a:=by
       intro q g' hq hRq a ha
       have hidx:gs[p+1+q]?=some g':=by
         have:gs=(pre++[g])++post:=by simp [hgs]
         rw [this,List.getElem?_append_right (by simp [hp])]
         simpa [hp,Nat.add_sub_cancel_left] using hq
       have hlen0:acc0.1.length=n+p+1:=by simp [hacc0,vi]
       rw [hlen0] at hRq
       exact q33 hidx (by simpa [nAA] using hRq) ha
     have hres:=q175 (wn n gs o) n (List.ofFn x) (by simp) post _ acc0 hok_post hR hinv0
     rw [← hsplit] at hres
     exact ⟨hres.2.1 o,(hres.2.2 o (q34 n gs o)).trans (hev x)⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=(hinv_all y).2
   have e2:=(hinv_all y').2
   rw [hst] at e1 e2
   exact e1.symm.trans e2
 | inr j =>
   obtain ⟨y,_,_⟩:=hnc
   have hj:=(hinv_all y).1
   rw [hst] at hj
   refine ⟨acc.2,j,hcl',hlen',hj,?_⟩
   intro x
   have e:=(hinv_all x).2
   rw [hst] at e
   exact e
structure MinClean (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ):Prop where
 hcl:yq n gs
 ho:o < n+gs.length
 hev:∀ x,val gs n o x=f x
 hreach:∀ p < gs.length,wn n gs o (n+p)
 hncG:∀ p < gs.length,∀ c:Bool,val gs n (n+p)≠fun _ => c
 hndup:∀ p < gs.length,∀ u < n+p,val gs n (n+p)≠val gs n u
open Classical in
lemma q56 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,MinClean n f gs o/\gs.length<=s:=by
 have hex:∃ k,∃ gs o,yq n gs/\gs.length=k/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
   obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=q48 n f s hnc h
   exact ⟨gs.length,gs,o,hcl,rfl,ho,hev⟩
 set k:=Nat.find hex with hk
 obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=Nat.find_spec hex
 have hle:k<=s:=by
   obtain ⟨gs0,o0,hcl0,hlen0,ho0,hev0⟩:=q48 n f s hnc h
   exact le_trans (Nat.find_min' hex ⟨gs0,o0,hcl0,rfl,ho0,hev0⟩) hlen0
 have hmin:∀ gs' o',yq n gs'->o' < n+gs'.length->(∀ x,val gs' n o' x=f x)->gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev'
   rw [hlen]
   exact Nat.find_min' hex ⟨gs',o',hcl',rfl,ho',hev'⟩
 refine ⟨gs,o,⟨hcl,ho,hev,?_,?_,?_⟩,by omega⟩
 . intro p hp
   by_contra hnr
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl false) trivial (Or.inr hnr)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp c heqc
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl c) trivial
       (Or.inl fun x => by rw [heqc];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp u hu hequ
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inr u) hu
       (Or.inl fun x => by
         rw [hequ];unfold val
         rw [zd,ve _ _ _ (by rw [qu];simp;omega)];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
def wf (n : ℕ) (v:Fin n):List Stat :=
 List.ofFn fun i:Fin n => if i=v then Sum.inl false else Sum.inr (i : ℕ)
lemma q139 (n : ℕ) (v:Fin n) (x:Fin n->Bool) :
   Inv n (List.ofFn x) (List.ofFn (Function.update x v false)) (wf n v,[]):=by
 refine ⟨by simp [wf],?_⟩
 intro i
 by_cases hlt:i < n
 . by_cases hiv:(⟨i,hlt⟩:Fin n)=v
   . subst hiv;simp [wf,hlt,qn,ze]
   . simp [wf,hlt,hiv,qn,ze,q3,fUN hiv]
 . rw [lGD _ _ (by simp [wf];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma wz (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (v:Fin n) (B : ℕ)
   (hcl:yq n gs) (hev:∀ x,val gs n o x=f x)
   (hnc0:∃ x y:Fin n->Bool,f (Function.update x v false)≠f (Function.update y v false))
   (hlb:∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->B<=s') :
   (∀ c,(elim n gs (wf n v,[])).1.getD o (Sum.inl false)≠Sum.inl c) /\
   B<=(elim n gs (wf n v,[])).2.length:=by
 set acc:=elim n gs (wf n v,[]) with hacc
 have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) acc :=
   fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hcl g hg).1) (q139 n v x)
 have hval:∀ x,ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))
     = f (Function.update x v false):=fun x => ((hinv x).2 o).2.trans (hev _)
 have hno:∀ c,acc.1.getD o (Sum.inl false)≠Sum.inl c:=by
   intro c hc
   obtain ⟨x,y,hne⟩:=hnc0
   apply hne
   rw [← hval x,← hval y,hc];rfl
 refine ⟨hno,?_⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c => exact absurd hst (hno c)
 | inr j =>
   apply hlb acc.2.length
   refine ⟨⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro x;have:=hval x;rw [hst] at this;exact this
lemma k3 (n u w : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->u < acc.1.length->w < acc.1.length ->
   (∃ cu,acc.1.getD u (Sum.inl false)=Sum.inl cu) ->
   (∃ cw,acc.1.getD w (Sum.inl false)=Sum.inl cw) ->
   (∃ g₁ ∈ gs,u ∈ g₁.inputs) ->
   (∃ g₂ ∈ gs,w ∈ g₂.inputs) ->
   (∀ g ∈ gs,¬ (u ∈ g.inputs/\w ∈ g.inputs)) ->
   (elim n gs acc).2.length+2<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ _ _ h1 _ _;obtain ⟨g,hg,_⟩:=h1;simp at hg
 | cons g gs ih =>
   intro acc hok hu hw hcu hcw hg1 hg2 hdisj
   rw [k4,lLC]
   have hgn:NOk g:=hok g List.mem_cons_self
   have hgsn:∀ g' ∈ gs,NOk g':=fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
   by_cases hug:u ∈ g.inputs
   . have hwg:w ∉ g.inputs:=fun h => hdisj g List.mem_cons_self ⟨hug,h⟩
     obtain ⟨cu,hcu⟩:=hcu
     have h0:=vs n acc g hgn u hug cu hcu
     have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
       obtain ⟨g',hg',hw'⟩:=hg2
       rcases List.mem_cons.1 hg' with rfl | hmem
       . exact absurd hw' hwg
       . exact ⟨g',hmem,hw'⟩
     have h1:=zt n w gs (qa n acc g) hgsn (by simp [qa];omega)
       (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
       hg2'
     omega
   . by_cases hwg:w ∈ g.inputs
     . obtain ⟨cw,hcw⟩:=hcw
       have h0:=vs n acc g hgn w hwg cw hcw
       have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have h1:=zt n u gs (qa n acc g) hgsn (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         hg1'
       omega
     . have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
         obtain ⟨g',hg',hw'⟩:=hg2
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hw' hwg
         . exact ⟨g',hmem,hw'⟩
       have h1:=ih (qa n acc g) hgsn (by simp [qa];omega) (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
         hg1' hg2' (fun g' hg' => hdisj g' (List.mem_cons_of_mem _ hg'))
       have h2:(qa n acc g).2.length<=acc.2.length+1:=by
         simp only [qa,lLA]
         have:=y2 (qg g.op (n+acc.2.length)
           (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
         omega
       omega
inductive TagRun {α:Type} (inv : α->α) (meet join : α->α->α) (zero one goal : α) :
   ℕ->List (α × ℕ)->Prop where
 | done (tg : ℕ):TagRun inv meet join zero one goal 0 [(goal,tg)]
 | perm {s xs zs}:List.Perm xs zs ->
     TagRun inv meet join zero one goal s xs ->
     TagRun inv meet join zero one goal s zs
 | uNot {s a ta r} (save:Bool) :
     ta≠1->ta≠2->(ta=3->save=false) ->
     inv a≠zero->inv a≠one->inv a≠a->(∀ x ∈ r,x.1≠inv a) ->
     TagRun inv meet join zero one goal s
       ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Bool) :
     ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
     join a b≠zero->join a b≠one ->
     join a b≠a->join a b≠b->(∀ x ∈ r,x.1≠join a b) ->
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Bool) :
     ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
     meet a b≠zero->meet a b≠one ->
     meet a b≠a->meet a b≠b->(∀ x ∈ r,x.1≠meet a b) ->
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
lemma TagRun.toRun {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   Run inv meet join goal s (ws.map Prod.fst):=by
 induction h with
 | done _ => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map Prod.fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   have e:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst)
       = (if true then inv a else a)::qk save a (r.map Prod.fst):=by
     cases save <;> simp [qk]
   rw [e] at ih
   exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst)
       = (if false then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map Prod.fst)
       = (if true then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two true ka kb ih
lemma TagRun.len_le {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   ws.length<=s+1:=by
 have:=q202 h.toRun
 simpa using this
lemma TagRun.map {α β:Type} (e : α->β) (hinj:Function.Injective e)
   {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {inv' : β->β} {meet' join' : β->β->β} {zero' one' goal' : β}
   (h0:e zero=zero') (h1:e one=one') (hg:e goal=goal')
   (hi:∀ a,e (inv a)=inv' (e a))
   (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   TagRun inv' meet' join' zero' one' goal' s (ws.map fun p => (e p.1,p.2)):=by
 induction h with
 | done tg => rw [← hg];exact TagRun.done tg
 | perm hp _ ih => exact TagRun.perm (hp.map _) ih
 | @uNot s a ta r save h1t h2t h3t hnz hno hna hnr _ ih =>
   have e1:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fun p => (e p.1,p.2))
       = (inv' (e a),if ta=3 then 2 else 0)::qk save (e a,0) (r.map fun p => (e p.1,p.2)):=by
     cases save <;> simp [qk,hi]
   rw [e1] at ih
   refine TagRun.uNot save h1t h2t h3t ?_ ?_ ?_ ?_ ih
   . rw [← hi,← h0];exact fun h => hnz (hinj h)
   . rw [← hi,← h1];exact fun h => hno (hinj h)
   . rw [← hi];exact fun h => hna (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hi];exact fun h => hnr y hy (hinj h)
 | @bOr s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fun p => (e p.1,p.2))
       = (join' (e a) (e b),0)::qk ka (e a,if ta=3 then 1 else 0) (qk kb (e b,if tb=3 then 1 else 0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hj]
   rw [e1] at ih
   refine TagRun.bOr ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hj,← h0];exact fun h => hnz (hinj h)
   . rw [← hj,← h1];exact fun h => hno (hinj h)
   . rw [← hj];exact fun h => hna (hinj h)
   . rw [← hj];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hj];exact fun h => hnr y hy (hinj h)
 | @bAnd s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fun p => (e p.1,p.2))
       = (meet' (e a) (e b),if ta=3\/tb=3 then 1 else 0)::qk ka (e a,0) (qk kb (e b,0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hm]
   rw [e1] at ih
   refine TagRun.bAnd ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hm,← h0];exact fun h => hnz (hinj h)
   . rw [← hm,← h1];exact fun h => hno (hinj h)
   . rw [← hm];exact fun h => hna (hinj h)
   . rw [← hm];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hm];exact fun h => hnr y hy (hinj h)
def v3 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ):List Stat × List Gate :=
 elim n (gs.take p) (wf n v,[])
lemma vb (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (hp:p<=gs.length) :
   (v3 n gs v p).1.length=n+p:=by
 unfold v3
 rw [q50]
 simp [wf,List.length_take,Nat.min_eq_left hp]
lemma q30 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (g:Gate) (hg:gs[p]?=some g) :
   v3 n gs v (p+1)=qa n (v3 n gs v p) g:=by
 unfold v3
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 rw [List.take_succ_eq_append_getElem hlt,hge,jz,k4]
 rfl
lemma zj (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) :
   elim n (gs.drop p) (v3 n gs v p)=elim n gs (wf n v,[]):=by
 unfold v3
 rw [← jz,List.take_append_drop]
def yf (n : ℕ) (gs:List Gate) (f:BFn n) (p a tg : ℕ):Prop :=
 match tg with
 | 0 => True
 | 1 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 2 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl true /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 3 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+2
 | _ => False
lemma q12 {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ}
   (h:yf n gs f p a tg):tg<=3:=by
 match tg with
 | 0 | 1 | 2 | 3 => omega
 | _+4 => exact False.elim h
lemma vv {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ} {g:Gate}
   (hg:gs[p]?=some g) (ha:a < n+p) (h:yf n gs f p a tg) :
   yf n gs f (p+1) a tg:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 have hdrop:gs.drop p=g::gs.drop (p+1):=by rw [List.drop_eq_getElem_cons hlt,hge]
 have step_aux:∀ v c B,
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl c ->
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
     (v3 n gs v (p+1)).1.getD a (Sum.inl false)=Sum.inl c /\
     (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length <=
       (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
   intro v c B hget hbd
   have hsucc:=q30 n gs v p g hg
   have hfl:=vb n gs v p (by omega)
   constructor
   . rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
   . have heq:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
       rw [zj,zj]
     have hlen2:(v3 n gs v (p+1)).2.length<=(v3 n gs v p).2.length+1:=by
       rw [hsucc];simp only [qa,lLA]
       have:=y2 (qg g.op (n+(v3 n gs v p).2.length)
         (g.inputs.map fun i => (v3 n gs v p).1.getD i (Sum.inl false))).1
       omega
     have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
     rw [heq];omega
 match tg with
 | 0 => trivial
 | 1 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 1 hget hbd⟩
 | 2 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v true 1 hget hbd⟩
 | 3 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 2 hget hbd⟩
 | _+4 => exact False.elim h
lemma zr {n : ℕ} {gs:List Gate} {o p u : ℕ} {f:BFn n} {v:Fin n} {c:Bool}
   (hm:MinClean n f gs o) (hp:p<=gs.length)
   (hlive:u ∈ liveList gs n o p)
   (hnc:∃ x y,f (Function.update x v false)≠f (Function.update y v false))
   (hconst:(v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c) :
   ∃ g' ∈ gs.drop p,u ∈ g'.inputs:=by
 have ⟨hlt,hl⟩:=(qw gs n o p u).1 hlive
 rcases hl with rfl | ⟨q,hq,g',hg',hin,_⟩
 . exfalso
   have hfl:=vb n gs v p hp
   have heq:(elim n gs (wf n v,[])).1.getD u (Sum.inl false)=Sum.inl c:=by
     rw [← zj n gs v p,wy n u _ _ _ (by omega)];exact hconst
   have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) (elim n gs (wf n v,[])) :=
     fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hm.hcl g hg).1) (q139 n v x)
   obtain ⟨x,y,hne⟩:=hnc
   apply hne
   have e1:=((hinv x).2 u).2.trans (hm.hev _)
   have e2:=((hinv y).2 u).2.trans (hm.hev _)
   rw [heq] at e1 e2
   exact e1.symm.trans e2
 . have hqlt:q < gs.length:=(List.getElem?_eq_some_iff.1 hg').1
   have hqeq:gs[q]=g':=(List.getElem?_eq_some_iff.1 hg').2
   refine ⟨g',?_,hin⟩
   have:g'=(gs.drop p)[q - p]'(by simp;omega):=by
     rw [List.getElem_drop];simp [show p+(q - p)=q by omega,hqeq]
   rw [this]
   exact List.getElem_mem _
lemma q21 {n : ℕ} {gs:List Gate} {o p j : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length)
   (hval:∀ x,val gs n (n+p) x=!(val gs n j x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by
   intro e;have h0:=hval (fun _ => false);rw [e] at h0
   cases hv:val gs n (n+p) (fun _ => false) <;> rw [hv] at h0 <;> cases h0
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;exact hne (hj.trans hnp.symm)
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hncG q hrlt false
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hncG q hrlt true
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
lemma q22 {n : ℕ} {gs:List Gate} {o p j k : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length) (hjlt:j < n+p)
   (hval:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by omega
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;omega
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hndup q hrlt (n+p) (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hndup q hrlt j (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
lemma q193 {n : ℕ} {gs:List Gate} (hcl:yq n gs) (p : ℕ) :
   ∀ g ∈ gs.drop p,NOk g:=fun g hg => ja hcl g (List.mem_of_mem_drop hg)
open Classical in
lemma q123 (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (hm:MinClean n f gs o) :
   ∀ d p,p+d=gs.length ->
     ∀ tg : ℕ->ℕ,(∀ a ∈ liveList gs n o p,yf n gs f p a (tg a)) ->
       TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f d
         ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
 intro d
 induction d with
 | zero =>
   intro p hp tg _
   have hperm : [o].Perm (liveList gs n o p):=by
     refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
     intro a
     rw [qw,List.mem_singleton]
     constructor
     . rintro rfl;exact ⟨by have:=hm.ho;omega,Or.inl rfl⟩
     . rintro ⟨_,h | ⟨q,hq,g',hg',_,_⟩⟩
       . exact h
       . have:=(List.getElem?_eq_some_iff.1 hg').1;omega
   have hf:val gs n o=f:=funext hm.hev
   have h1:([(f,tg o)]).Perm ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
     rw [← hf];exact hperm.map (fun a => (val gs n a,tg a))
   exact TagRun.perm h1 (TagRun.done (tg o))
 | succ d ih =>
   intro p hp tg hok
   have hplt:p < gs.length:=by omega
   obtain ⟨g,hg⟩:∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hplt⟩
   have hr:wn n gs o (n+p):=hm.hreach p hplt
   have hstep:=q73 n gs o hm.hcl p g hg hr
   have hin:∀ a ∈ g.inputs,a ∈ liveList gs n o p:=fun a ha =>
     (qw _ _ _ _ _).2 ⟨j2 (hm.hcl p g hg) a ha,Or.inr ⟨p,le_rfl,g,hg,ha,hr⟩⟩
   have hnew:∀ a ∈ liveList gs n o p,a≠n+p:=fun a ha =>
     Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
   have hvg:=q103 n gs p g hg (j2 (hm.hcl p g hg))
   have hnd0:=vy gs n o p
   have hdrop:gs.drop p=g::gs.drop (p+1):=by
     rw [List.drop_eq_getElem_cons hplt];have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2;rw [hge]
   have hgn:NOk g:=q101 (hm.hcl p g hg)
   have hdrop_nok:=q193 hm.hcl (p+1)
   have hnz:val gs n (n+p)≠fun _ => false:=hm.hncG p hplt false
   have hno:val gs n (n+p)≠fun _ => true:=hm.hncG p hplt true
   have hnd:∀ a ∈ liveList gs n o p,val gs n a≠val gs n (n+p):=fun a ha e =>
     hm.hndup p hplt a ((qw _ _ _ _ _).1 ha).1 e.symm
   rcases hm.hcl p g hg with ⟨hop,j,hj,hinp⟩ | ⟨hop,j,k,hj,hk,hinp⟩
   ·
     have hjm:j ∈ liveList gs n o p:=hin j (by simp [hinp])
     have hval:val gs n (n+p)=invF (val gs n j):=by
       funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
     have hsave_not:∀ v c B,
         (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
         (v3 n gs v p).1.getD j (Sum.inl false)=Sum.inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
         2<=B /\
         (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c) /\
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (q11 n gs o (p+1) j->3<=B):=by
       intro v c B hncv hget hbd
       have hsucc:=q30 n gs v p g hg
       have hfl:=vb n gs v p (by omega)
       have hfl1:=vb n gs v (p+1) (by omega)
       have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
         rw [hsucc];exact vs n _ g hgn j (by simp [hinp]) c hget
       have hout_c:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c):=by
         rw [hsucc];simp only [qa]
         rw [z2 _ _ _ _ hfl,hop,hinp]
         simp only [lMC,List.map_nil,hget,qg,wr]
       have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
         rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
       have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw [heq_e,h0];omega
       have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
       have hread_np:=zr hm (by omega) hnp_live hncv hout_c
       have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
         (by omega) ⟨!c,hout_c⟩ hread_np
       refine ⟨by omega,hout_c,hbd1,?_⟩
       intro hjlive
       have hj_live1:j ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hjlive⟩
       have hj_c1:(v3 n gs v (p+1)).1.getD j (Sum.inl false)=Sum.inl c:=by
         rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
       have hread_j:=zr hm (by omega) hj_live1 hncv hj_c1
       have hdisj:=q21 hm hplt (fun x => congrFun hval x)
       have hkill2:=k3 n j (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
         hdrop_nok (by omega) (by omega) ⟨c,hj_c1⟩ ⟨!c,hout_c⟩ hread_j hread_np hdisj
       omega
     have ht1:tg j≠1:=by
       intro h1;have hw:=hok j hjm;rw [h1] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 1 hncv hget hbd).1;omega
     have ht2:tg j≠2:=by
       intro h2;have hw:=hok j hjm;rw [h2] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v true 1 hncv hget hbd).1;omega
     have ht3:tg j=3->decide (q11 n gs o (p+1) j)=false:=by
       intro h3;simp only [decide_eq_false_iff_not];intro hjlive
       have hw:=hok j hjm;rw [h3] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 2 hncv hget hbd).2.2.2 hjlive;omega
     set tg' : ℕ->ℕ:=fun a =>
       if a=n+p then (if tg j=3 then 2 else 0)
       else if a=j then 0
       else tg a
     have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
       intro a ha
       simp only [tg']
       by_cases hanp:a=n+p
       . subst hanp;simp only [↓reduceIte]
         by_cases h3:tg j=3
         . simp only [h3,↓reduceIte]
           have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           obtain ⟨_,hout_c,hbd1,_⟩:=hsave_not v false 2 hncv hget hbd
           exact ⟨v,hncv,hout_c,by omega⟩
         . simp only [h3,↓reduceIte];trivial
       . simp only [hanp,↓reduceIte]
         by_cases haj:a=j
         . simp only [haj,↓reduceIte];trivial
         . simp only [haj,↓reduceIte]
           have ha0:a ∈ liveList gs n o p:=by
             rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
             . exact absurd rfl hanp
             . exact h1
           exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
     have IH:=ih (p+1) (by omega) tg' hok'
     have hp1:(liveList gs n o p).Perm (j::(liveList gs n o p).erase j):=List.perm_cons_erase hjm
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
         rw [wa];rintro (⟨_,h⟩ | h)
         . exact hnew j hjm h.symm
         . exact hnew _ (List.mem_of_mem_erase h) rfl
       . intro a
         rw [hstep a,lMM,wa,hnd0.mem_erase_iff,hinp,List.mem_singleton]
         simp only [decide_eq_true_eq]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 haj,haj⟩)
             . exact Or.inr (Or.inr ⟨haj,h1⟩)
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,h2⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨h2,fun h => absurd h h1⟩
     have hmap_rest:((liveList gs n o p).erase j).map (fun a => (val gs n a,tg' a)) =
         ((liveList gs n o p).erase j).map (fun a => (val gs n a,tg a)):=by
       apply List.map_congr_left
       intro a ha
       have h1:a≠j:=(hnd0.mem_erase_iff.1 ha).1
       have h2:a≠n+p:=hnew a (List.mem_of_mem_erase ha)
       simp [tg',h1,h2]
     have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)).map (fun a => (val gs n a,tg' a)) =
         qk (decide (q11 n gs o (p+1) j)) (val gs n j,0) (((liveList gs n o p).erase j).map fun a => (val gs n a,tg a)):=by
       rw [wd,hmap_rest]
       have hjne:j≠n+p:=by omega
       simp [tg',hjne]
     have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
     rw [lMC,hmap_kept,hval] at IH'
     have htgnp:tg' (n+p)=(if tg j=3 then 2 else 0):=by simp [tg']
     rw [htgnp] at IH'
     refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
     refine TagRun.uNot (decide (q11 n gs o (p+1) j)) ht1 ht2 ht3
       (hval ▸ hnz) (hval ▸ hno) (fun e => hnd j hjm (hval ▸ e.symm)) ?_ IH'
     intro x hx
     obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
     exact hval ▸ hnd a (List.mem_of_mem_erase ha)
   ·
     have hjk:j≠k:=by
       intro e;subst e
       apply hm.hndup p hplt j hj
       funext x;rw [hvg x,hinp]
       rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
     have hjm:=hin j (by simp [hinp])
     have hkm:=hin k (by simp [hinp])
     have hke:k ∈ (liveList gs n o p).erase j:=(hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm,hkm⟩
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hnr2:(((liveList gs n o p).erase j).erase k).Nodup:=hnr.erase k
     have hp1:(liveList gs n o p).Perm (j::k::((liveList gs n o p).erase j).erase k) :=
       (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
     have hmr:∀ a,a ∈ ((liveList gs n o p).erase j).erase k ↔ a≠k/\a≠j/\a ∈ liveList gs n o p:=by
       intro a;rw [hnr.mem_erase_iff,hnd0.mem_erase_iff]
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k
             (((liveList gs n o p).erase j).erase k))):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ (q36 _ _ _ hnr2 ?_) ?_⟩
         . rw [wa,wa]
           rintro (⟨_,h⟩ | ⟨_,h⟩ | h)
           . exact hnew j hjm h.symm
           . exact hnew k hkm h.symm
           . exact hnew _ ((hmr _).1 h).2.2 rfl
         . rw [hmr];simp
         . rw [wa,hmr]
           rintro (⟨_,h⟩ | h)
           . exact hjk h
           . exact h.2.1 rfl
       . intro a
         rw [hstep a,lMM,wa,wa,hmr a]
         simp only [decide_eq_true_eq,hinp,lMM,List.not_mem_nil,or_false]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj),haj⟩)
             . by_cases hak:a=k
               . exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak),hak⟩))
               . exact Or.inr (Or.inr (Or.inr ⟨hak,haj,h1⟩))
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,rfl⟩ | ⟨h1,h2,h3⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨hkm,fun _ => h1⟩
           . exact Or.inr ⟨h3,fun h => by rcases h with h | h <;> contradiction⟩
     rcases hop with hop | hop
     ·
       have hval:val gs n (n+p)=meetF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hand_const:∀ (u w_other : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (hval_u:∀ x,val gs n (n+p) x=(val gs n u x&&val gs n w_other x))
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=false ->
             2<=B /\
             (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false /\
             (q11 n gs o (p+1) u->3<=B)) /\
           (c=true->q11 n gs o (p+1) u->2<=B):=by
         intro u wo hu hult hvalu v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hbd1,?_,?_⟩
         . intro hcf;subst hcf
           have hout_f:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ko]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ko]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_f
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hout_f⟩ hread_np
           refine ⟨by omega,hout_f,?_⟩
           intro hulive
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hdisj:=q22 hm hplt hult hvalu
           have hkill2:=k3 n u (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
             hdrop_nok (by omega) (by omega) ⟨false,hu_c1⟩ ⟨false,hout_f⟩ hread_u hread_np hdisj
           omega
         . intro hct hulive;subst hct
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hu_c1⟩ hread_u
           omega
       have hval_j:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x):=fun x => congrFun hval x
       have hval_k:∀ x,val gs n (n+p) x=(val gs n k x&&val gs n j x):=fun x => by
         rw [hval_j x,Bool.and_comm]
       have hta1:tg j≠1:=by
         intro h1;have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const j k (by simp [hinp]) hj hval_j v false 1 hncv hget hbd).2.1 rfl
         omega
       have htb1:tg k≠1:=by
         intro h1;have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const k j (by simp [hinp]) hk hval_k v false 1 hncv hget hbd).2.1 rfl
         omega
       have hta_save:tg j=1\/tg j=2\/tg j=3->decide (q11 n gs o (p+1) j)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hjlive
         rcases h123 with h1 | h2 | h3
         . exact hta1 h1
         . have hw:=hok j hjm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const j k (by simp [hinp]) hj hval_j v true 1 hncv hget hbd).2.2 rfl hjlive;omega
         . have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd).2.1 rfl).2.2 hjlive;omega
       have htb_save:tg k=1\/tg k=2\/tg k=3->decide (q11 n gs o (p+1) k)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hklive
         rcases h123 with h1 | h2 | h3
         . exact htb1 h1
         . have hw:=hok k hkm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const k j (by simp [hinp]) hk hval_k v true 1 hncv hget hbd).2.2 rfl hklive;omega
         . have hw:=hok k hkm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd).2.1 rfl).2.2 hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then (if tg j=3\/tg k=3 then 1 else 0)
         else if a=j\/a=k then 0
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . subst hanp;simp only [↓reduceIte]
           by_cases h3:tg j=3\/tg k=3
           . simp only [h3,↓reduceIte]
             rcases h3 with hj3 | hk3
             . have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
             . have hw:=hok k hkm;rw [hk3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
           . simp only [h3,↓reduceIte];trivial
         . simp only [hanp,↓reduceIte]
           by_cases hajk:a=j\/a=k
           . simp only [hajk,↓reduceIte];trivial
           . simp only [hajk,↓reduceIte]
             have ha0:a ∈ liveList gs n o p:=by
               rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
               . exact absurd rfl hanp
               . exact h1
             exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         simp [tg',hjne,hkne]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=(if tg j=3\/tg k=3 then 1 else 0):=by simp [tg']
       rw [htgnp] at IH'
       have hjle3:=q12 (hok j hjm)
       have hkle3:=q12 (hok k hkm)
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bAnd (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta1 htb1 (fun h => hta_save (by omega)) (fun h => htb_save (by omega))
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
     ·
       have hval:val gs n (n+p)=joinF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hor_const:∀ (u : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c /\
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=true->2<=B) /\
           (c=false->q11 n gs o (p+1) u->2<=B):=by
         intro u hu hult v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hu_c1,hbd1,?_,?_⟩
         . intro hct;subst hct
           have hout_t:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl true:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ji]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ji]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_t
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hout_t⟩ hread_np
           omega
         . intro hcf hulive;subst hcf
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hu_c1⟩ hread_u
           omega
       have hta2:tg j≠2:=by
         intro h2;have hw:=hok j hjm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v true 1 hncv hget hbd).2.2.1 rfl;omega
       have htb2:tg k≠2:=by
         intro h2;have hw:=hok k hkm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v true 1 hncv hget hbd).2.2.1 rfl;omega
       have hta1:tg j=1->decide (q11 n gs o (p+1) j)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hjlive
         have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v false 1 hncv hget hbd).2.2.2 rfl hjlive;omega
       have htb1:tg k=1->decide (q11 n gs o (p+1) k)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hklive
         have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v false 1 hncv hget hbd).2.2.2 rfl hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then 0
         else if a=j then (if tg j=3 then 1 else 0)
         else if a=k then (if tg k=3 then 1 else 0)
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . simp [hanp,yf]
         . simp only [hanp,↓reduceIte]
           by_cases haj:a=j
           . rw [haj];simp only [↓reduceIte]
             by_cases hj3:tg j=3
             . simp only [hj3,↓reduceIte]
               have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hor_const j (by simp [hinp]) hj v false 2 hncv hget hbd
               exact ⟨v,hncv,hh.1,by omega⟩
             . simp only [hj3,↓reduceIte];trivial
           . simp only [haj,↓reduceIte]
             by_cases hak:a=k
             . rw [hak];simp only [↓reduceIte]
               by_cases hk3:tg k=3
               . simp only [hk3,↓reduceIte]
                 have hw:=hok k hkm;rw [hk3] at hw
                 obtain ⟨v,hncv,hget,hbd⟩:=hw
                 have hh:=hor_const k (by simp [hinp]) hk v false 2 hncv hget hbd
                 exact ⟨v,hncv,hh.1,by omega⟩
               . simp only [hk3,↓reduceIte];trivial
             . simp only [hak,↓reduceIte]
               have ha0:a ∈ liveList gs n o p:=by
                 rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
                 . exact absurd rfl hanp
                 . exact h1
               exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,if tg j=3 then 1 else 0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,if tg k=3 then 1 else 0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         have hkj:k≠j:=fun e => hjk e.symm
         simp [tg',hjne,hkne,hkj]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=0:=by simp [tg']
       rw [htgnp] at IH'
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bOr (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta2 htb2 hta1 htb1
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
lemma q133 {n : ℕ} {gs:List Gate} {o : ℕ} {f:BFn n}
   (hev:∀ x,val gs n o x=f x) (v:Fin n)
   (hdep:∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x) :
   (v : ℕ) ∈ liveList gs n o 0:=by
 rw [qw]
 refine ⟨by omega,?_⟩
 by_contra hnl
 have hnr : ¬ wn n gs o (v : ℕ):=by
   intro hr
   rcases q66 hr with heq | ⟨q,g,hg,hin,hrq⟩
   . exact hnl (Or.inl heq)
   . exact hnl (Or.inr ⟨q,nZL q,g,hg,hin,hrq⟩)
 obtain ⟨x,hx⟩:=hdep
 apply hx
 rw [← hev,← hev]
 have hagree:∀ (p : ℕ),∀ i < n+p,wn n gs o i ->
     (q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).getD i false =
     (q3 (gs.take p) (List.ofFn x)).getD i false:=by
   intro p
   induction p with
   | zero =>
     intro i hi hr
     simp only [List.take_zero,q3,List.foldl_nil]
     have hlt:i < n:=by omega
     have hne:(⟨i,hlt⟩:Fin n)≠v:=fun e => hnr (by simpa [← e] using hr)
     simp [hlt,fUN hne]
   | succ p ih =>
     intro i hi hr
     by_cases hp:p < gs.length
     . have htake:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem hp
       rw [htake,zd,zd]
       have hlen1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       have hlen2:(q3 (gs.take p) (List.ofFn x)).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       by_cases hip:i=n+p
       . subst hip
         show (q3 (gs.take p) _++[_]).getD (n+p) false=(q3 (gs.take p) _++[_]).getD (n+p) false
         rw [z2 _ _ _ _ hlen1,z2 _ _ _ _ hlen2]
         congr 1
         apply List.map_congr_left
         intro a ha
         have hra:wn n gs o a:=q33 (List.getElem?_eq_getElem hp) hr ha
         by_cases halt:a < n+p
         . exact ih a halt hra
         . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
       . show (q3 (gs.take p) _++[_]).getD i false=(q3 (gs.take p) _++[_]).getD i false
         rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
         exact ih i (by omega) hr
     . have htake:gs.take (p+1)=gs.take p:=by
         rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
       rw [htake]
       by_cases hlt:i < n+p
       . exact ih i hlt hr
       . have hl1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         have hl2:(q3 (gs.take p) (List.ofFn x)).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         rw [lGD _ _ (by omega),lGD _ _ (by omega)]
 have ho_lt:o < n+gs.length:=by
   by_contra hge
   have hfalse:∀ y:Fin n->Bool,val gs n o y=false:=fun y =>
     lGD _ _ (by rw [qu];simp;omega)
   exact hx (by rw [← hev,← hev,hfalse,hfalse])
 have h:=hagree gs.length o ho_lt (q34 n gs o)
 rw [List.take_length] at h
 exact h
open Classical in
lemma q88 {n : ℕ} (f:BFn n) (cap : ℕ) (initTags:Fin n->ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (hdep:∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s'))
   (s : ℕ) (hs:s<=cap) (hc:HasCircuitSize n f s) :
   ∃ s',s'<=cap /\
     TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s'
       (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)):=by
 obtain ⟨gs,o,hm,hlen⟩:=q56 n f s hnc hc
 have hlive0:liveList gs n o 0=List.range n:=by
   have hsub:=(List.filter_sublist (l:=List.range (n+0)) (p:=fun a => decide (q11 n gs o 0 a)))
   simp only [nAZ] at hsub
   refine List.Sublist.eq_of_length hsub ?_
   have hperm:(List.range n).Perm (liveList gs n o 0):=by
     refine (List.perm_ext_iff_of_nodup List.nodup_range (vy gs n o 0)).2 ?_
     intro a
     rw [List.mem_range]
     constructor
     . intro ha;exact q133 hm.hev ⟨a,ha⟩ (hdep ⟨a,ha⟩)
     . intro ha;exact by simpa using ((qw gs n o 0 a).1 ha).1
   exact hperm.length_eq.symm
 set tg : ℕ->ℕ:=fun a => if h:a < n then initTags ⟨a,h⟩ else 0
 have hok0:∀ a ∈ liveList gs n o 0,yf n gs f 0 a (tg a):=by
   intro a ha
   rw [hlive0,List.mem_range] at ha
   have hta:tg a=initTags ⟨a,ha⟩:=by simp [tg,ha]
   rw [hta]
   rcases htag ⟨a,ha⟩ with h0 | ⟨h1,hnc0,hlb⟩ | ⟨h3,hnc0,hlb⟩
   . rw [h0];trivial
   . rw [h1]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 1) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
   . rw [h3]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 2) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
 have htr:=q123 n f gs o hm gs.length 0 (by omega) tg hok0
 refine ⟨gs.length,by omega,?_⟩
 have heq:(liveList gs n o 0).map (fun a => (val gs n a,tg a)) =
     List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i):=by
   rw [hlive0]
   apply List.ext_getElem
   . simp
   . intro i h1 h2
     have hi:i < n:=by simpa using h2
     simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
     exact Prod.ext (q172 gs n ⟨i,hi⟩) (by simp [tg,hi])
 rw [← heq]
 exact htr
def zm {α:Type} (x:Nat) (f:Nat->α) : α :=
 match x with
 | 0 => f 0
 | n+1 => f (Nat.succ n)
lemma v5 {α:Type} (x:Nat) (f:Nat->α):zm x f=f x:=by
 cases x <;> rfl
structure Cfg where
 k:Nat
 sh0:Nat
 sh1:Nat
 shTT:Nat
 all1v:Nat
 goalv:Nat
 lok:Nat
 m0all:Nat
 m0:Nat
 a29_0:Nat
 b5_0:Nat
 m1:Nat
 m12:Nat
 a29_1:Nat
 b5_1:Nat
def q76 (sw:Nat × Nat × Nat × Nat) (w:Nat):Nat :=
 let (d,m01,m10,mEq):=sw
 Nat.lor (Nat.lor (Nat.land w mEq) (Nat.shiftRight (Nat.land w m01) d))
         (Nat.shiftLeft (Nat.land w m10) d)
def ym:List (Nat × Nat × Nat × Nat)->Nat->Nat
 | [],w => w
 | sw::rest,w => ym rest (q76 sw w)
def q72 (sh:Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (Nat.shiftRight w sh) fun v => (v,tg)::q72 sh rest
def wx (g:List (Nat × Nat × Nat × Nat)):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (ym g w) fun v => (v,tg)::wx g rest
def M128:Nat:=0x9e3779b97f4a7c15f39cc0605cedc835
def q211:Nat:=0x517cc1b727220a95b3650d1e9a87c3f1
def q210:Nat:=0xbf58476d1ce4e5b994d049bb133111eb
def q209:Nat:=0x2545f4914f6cdd1d6c62272e07bb0142
def q208 (salt w tg:Nat):Nat :=
 let s:=match tg with
   | 0 => salt
   | 1 => Nat.xor salt q211
   | 2 => Nat.xor salt q210
   | _ => Nat.xor salt q209
 zm (Nat.xor (Nat.xor w (Nat.shiftRight w 61)) s) fun x =>
 Nat.shiftRight (Nat.mul x (Nat.xor x M128)) 104
def q199 (salt:Nat):Nat->List (Nat × Nat)->Nat
 | acc,[] => acc
 | acc,(w,tg)::rest => zm (Nat.add acc (q208 salt w tg)) fun acc' => q199 salt acc' rest
def q75 (salt:Nat) (ws:List (Nat × Nat)):Nat:=Nat.land (q199 salt 0 ws) 0xFFFFFF
def q205 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 24 i)) 0xFFFFFF
def q192 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 32 i)) 0xFFFFFFFF
def q167 (T h:Nat):Nat->Nat->Nat->Nat
 | 0,lo,_ => lo
 | fuel+1,lo,hi =>
   if Nat.ble (Nat.add lo 2) hi then
     zm (Nat.div (Nat.add lo hi) 2) fun mid =>
     if Nat.ble (q205 T mid) h then q167 T h fuel mid hi else q167 T h fuel lo mid
   else lo
def q85 (NN FL HT:Nat->Nat) (s h:Nat):Nat :=
 let n:=NN s
 if Nat.beq n 0 then 999999
 else
   let ht:=HT s
   zm (q167 ht h (FL s) 0 n) fun j =>
   if Nat.beq (q205 ht j) h then j else 999999
def twEq (a b:Nat × Nat):Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
def jy (x:Nat × Nat):List (Nat × Nat)->Option (List (Nat × Nat))
 | [] => none
 | a::rest =>
   if twEq x a then some rest
   else match jy x rest with
     | none => none
     | some r => some (a::r)
def jk:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],[] => true
 | a::as,bs => match jy a bs with
   | none => false
   | some bs' => jk as bs'
 | _,_ => false
def twLt (a b:Nat × Nat):Bool :=
 if Nat.beq a.1 b.1 then Nat.blt a.2 b.2 else Nat.blt a.1 b.1
def q62 (x:Nat × Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => [x]
 | a::rest => if twLt x a then x::a::rest else a::q62 x rest
def q125:List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | a::rest => q62 a (q125 rest)
def q158:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],_ => false
 | _,[] => false
 | a::as,b::bs =>
   if twEq a b then q158 as bs else twLt a b
def q69 (g:List (Nat × Nat × Nat × Nat)) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let ws':=q125 (wx g ws)
 if q158 ws' ws then ws' else ws
def q35:List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->List (Nat × Nat)
 | [],ws => ws
 | g::rest,ws => q35 rest (q69 g ws)
def q186 (gens:List (List (Nat × Nat × Nat × Nat))) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let s0:=q125 ws
 match gens with
 | [] => s0
 | [g] => q69 g s0
 | _ => q35 gens (q35 gens s0)
def qi (m0 w0:Nat):Nat :=
 zm (Nat.land w0 m0) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m0) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m0) fun c =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 3) m0)) fun nd =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 4) m0)) fun ne =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 5) m0)) fun nf =>
 Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
         (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
def yg (sh1 m1 m12 w:Nat):Nat :=
 zm (Nat.shiftRight w sh1) fun w0 =>
 zm (Nat.land w0 m1) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m1) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m1) fun c =>
 zm (Nat.land (Nat.shiftRight w0 3) m1) fun d =>
 zm (Nat.land (Nat.shiftRight w0 4) m1) fun e =>
 zm (Nat.land (Nat.shiftRight w0 5) m1) fun f =>
 zm (Nat.xor m1 d) fun nd =>
 zm (Nat.xor m1 e) fun ne =>
 zm (Nat.xor m1 f) fun nf =>
 zm (Nat.xor m1 a) fun na =>
 zm (Nat.xor m1 b) fun nb =>
 zm (Nat.xor m1 c) fun nc =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))) fun v1 =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))) fun v2 =>
 zm (Nat.lor v1 v2) fun u =>
 zm (Nat.land u m12) fun hi =>
 Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                     (Nat.land (Nat.land u m1) (Nat.xor m1 (Nat.shiftRight hi 1))))
inductive PList where
 | nil:PList
 | cons (w tg alo ahi nahi cw uw a0 v0w v1w postC postU postV0 postV1:Nat) (tail:PList):PList
def kt (c:Cfg):List (Nat × Nat)->Nat × Nat × Nat × Nat × PList
 | [] => (0,0,0,0,PList.nil)
 | (w,tg)::rest =>
   let (pC,pU,pV0,pV1,tl):=kt c rest
   let alo:=Nat.land w c.lok
   let ahi:=Nat.land (Nat.shiftRight w c.k) c.lok
   let nahi:=Nat.xor c.lok ahi
   let cw:=Nat.xor alo ahi
   let uw:=Nat.land cw ahi
   let a0:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
   let v0w:=qi c.m0 a0
   let v1w:=yg c.sh1 c.m1 c.m12 w
   (Nat.lor cw pC,Nat.lor uw pU,Nat.add v0w pV0,Nat.add v1w pV1,
    PList.cons w tg alo ahi nahi cw uw a0 v0w v1w pC pU pV0 pV1 tl)
def q164:List (Nat × Nat)->Nat
 | [] => 0
 | _::rest => Nat.add 1 (q164 rest)
def yz (x:Nat):List (Nat × Nat)->Bool
 | [] => false
 | (a,_)::rest => if Nat.beq x a then true else yz x rest
def qx:List (Nat × Nat)->List (Nat × Nat)->List (Nat × Nat)
 | [],ys => ys
 | a::xs,ys => qx xs (a::ys)
def pToList:PList->List (Nat × Nat)
 | PList.nil => []
 | PList.cons w tg _ _ _ _ _ _ _ _ _ _ _ _ tl => (w,tg)::pToList tl
def qj (all1v:Nat) (ws:List (Nat × Nat)) (w:Nat):Bool :=
 !(Nat.beq w 0)&&!(Nat.beq w all1v)&&!(yz w ws)
def qb (c:Cfg) (v0Acc v0w:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add (Nat.add v0Acc v0w) c.a29_0) c.b5_0) c.b5_0
def z3 (c:Cfg) (v1Tot:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add v1Tot c.a29_1) c.b5_1) c.b5_1
def ke (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     Nat.beq (Nat.land missU (Nat.lor alo blo)) 0 &&
     qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.lor a0 b0)) &&
     (let w:=Nat.lor a b;qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       Nat.beq (Nat.land missU (Nat.lor nahi nbhi)) 0 &&
       qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.land a0 b0)) &&
       (let w:=Nat.land a b;let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0;
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))))
     if andHit then true
     else ke c ws onSurv a ta alo nahi a0 pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post
def q98 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if ke c ws onSurv a ta alo nahi a0 pre preU preV0 [] suf then true
   else q98 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def vx (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0 v0a:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if okOrB&&qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else if okOrB&&!(Nat.beq tb 1) then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w &&
         onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if okAndB&&qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else if okAndB&&Nat.beq tb 0 then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w &&
           onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else false
     if andHit then true
     else vx c ws onSurv a ta alo nahi a0 v0a pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post
def js (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if vx c ws onSurv a ta alo nahi a0 v0a pre preU preV0 [] suf then true
   else js c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def we (c:Cfg) (ws:List (Nat × Nat))
   (a ta alo nahi a0 v0a:Nat):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | pmU,pmV0,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         (okOrB&&qj c.all1v ws w) ||
         (!(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
         (!(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
       else if okOrB&&!(Nat.beq tb 1) then
         qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws (Nat.lor a b)
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           (okAndB&&qj c.all1v ws w) ||
           (Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
           (Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
         else if okAndB&&Nat.beq tb 0 then
           qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws (Nat.land a b)
         else false
     if andHit then true
     else we c ws a ta alo nahi a0 v0a (Nat.lor pmU ub) (Nat.add pmV0 v0b) post
def q26 (c:Cfg) (ws:List (Nat × Nat)):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | preU,preV0,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if we c ws a ta alo nahi a0 v0a preU preV0 suf then true
   else q26 c ws (Nat.lor preU ua) (Nat.add preV0 v0a) suf
def w7 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ _ cw ua a0 v0a _ _ postU postV0 _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let uw:=Nat.land cw alo;
      Nat.beq (Nat.lor (Nat.lor preU postU) uw) c.lok &&
      qb c (Nat.add preV0 postV0) (qi c.m0 (Nat.xor a0 c.m0all)) &&
      (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
       qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))))
   if hit then true
   else w7 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def kd (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi a0 v0a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | pmC,pmU,pmV0,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
            qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else
         Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
         qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post)))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
              qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else
           Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
           qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post)))
     if andHit then true
     else kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV0 v0b) (Nat.add pmV1 v1b) ((b,tb)::mid) post
def q96 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 v0a v1a _ _ _ _ suf =>
   if kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre preC preU preV0 preV1 [] suf then true
   else q96 c ws hasUp onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def w6 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo _ _ ca ua a0 v0a v1a postC postU postV0 postV1 suf =>
   let hit :=
     if Nat.beq ta 1||Nat.beq ta 2 then false
     else
       let w:=Nat.xor a c.all1v
       let wt:=if Nat.beq ta 3 then 2 else 0
       let uw:=Nat.land ca alo
       let rC:=Nat.lor preC postC
       let rU:=Nat.lor preU postU
       let rV0:=Nat.add preV0 postV0
       let rV1:=Nat.add preV1 postV1
       (Nat.beq (Nat.lor rC ca) c.lok &&
        (Nat.beq (Nat.lor rU uw) c.lok||z3 c (Nat.add rV1 v1a)) &&
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&Nat.beq (Nat.lor rU ca) c.lok &&
        qb c (Nat.add rV0 v0a) (qi c.m0 (Nat.xor a0 c.m0all)) &&
        qj c.all1v ws w&&onSurv ((w,0)::(a,0)::qx pre (pToList suf)))
   if hit then true
   else w6 c ws onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def kc (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi ca a0 v1a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | pmC,pmU,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 _ v1b postC postU _ postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       let v1w:=yg c.sh1 c.m1 c.m12 w
       let ta':=if Nat.beq ta 3 then 1 else 0
       let tb':=if Nat.beq tb 3 then 1 else 0
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest)) ||
         (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&qb c totV0 (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))
       else
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         let v1w:=yg c.sh1 c.m1 c.m12 w
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest)) ||
           (Nat.beq ta 0&&Nat.beq tb 0&&qb c totV0 (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::ws))
         else
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest))
     if andHit then true
     else kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV1 v1b) ((b,tb)::mid) post
def q94 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | preC,preU,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 _ v1a _ _ _ _ suf =>
   if kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre preC preU preV1 [] suf then true
   else q94 c ws hasUp totV0 onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def w5 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta _ _ _ ca _ _ _ _ postC _ _ _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor (Nat.lor preC postC) ca) c.lok&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&onSurv ((w,0)::ws))))
   if hit then true
   else w5 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf
def k9 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi ca:Nat) (pre:List (Nat × Nat)):Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | pmC,mid,PList.cons b tb blo bhi _ cb _ _ _ _ postC _ _ _ post =>
   let rC:=Nat.lor pmC postC
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     (let w:=Nat.lor a b
      let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
      let ta':=if Nat.beq ta 3 then 1 else 0
      let tb':=if Nat.beq tb 3 then 1 else 0
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,0)::rest)) ||
       (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,0)::(a,ta')::rest)) ||
       (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,0)::(b,tb')::rest)) ||
       (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       (let w:=Nat.land a b
        let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
        let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
        qj c.all1v ws w &&
        ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,wt)::rest)) ||
         (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,wt)::(a,0)::rest)) ||
         (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,wt)::(b,0)::rest)) ||
         (Nat.beq ta 0&&Nat.beq tb 0&&onSurv ((w,0)::ws))))
     if andHit then true
     else k9 c ws onSurv a ta alo ahi ca pre (Nat.lor pmC cb) ((b,tb)::mid) post
def q92 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta alo ahi _ ca _ _ _ _ _ _ _ _ suf =>
   if k9 c ws onSurv a ta alo ahi ca pre preC [] suf then true
   else q92 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf
def j6 (c:Cfg) (ws:List (Nat × Nat)):Bool :=
 match ws with
 | [(a,_)] => Nat.beq (Nat.xor a c.all1v) c.goalv
 | [(a,_),(b,_)] => Nat.beq (Nat.lor a b) c.goalv||Nat.beq (Nat.land a b) c.goalv
 | _ => false
def scanAll (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws onSurv 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws onSurv 0 0 [] pl||q96 c ws hasUp onSurv 0 0 0 0 [] pl
     else hasUp&&js c ws onSurv 0 0 [] pl
   | 2 => w6 c ws onSurv 0 0 0 0 [] pl||q94 c ws hasUp totV0 onSurv 0 0 0 [] pl
   | _ => w5 c ws onSurv 0 [] pl||q92 c ws onSurv 0 [] pl
def scanInline (c:Cfg) (s:Nat) (ws:List (Nat × Nat)):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws (fun _ => true) 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws (fun _ => true) 0 0 [] pl||q96 c ws hasUp (fun _ => true) 0 0 0 0 [] pl
     else hasUp&&q26 c ws 0 0 pl
   | 2 => w6 c ws (fun _ => true) 0 0 0 0 [] pl||q94 c ws hasUp totV0 (fun _ => true) 0 0 0 [] pl
   | _ => w5 c ws (fun _ => true) 0 [] pl||q92 c ws (fun _ => true) 0 [] pl
def q42 (pid:Nat):Nat->Nat->Nat × Nat
 | 0,j => (0,j)
 | fuel+1,j =>
   let t:=Nat.div (Nat.mul (Nat.add j 1) j) 2
   if Nat.ble t pid then q42 pid fuel (Nat.add j 1)
   else (Nat.sub pid (Nat.div (Nat.mul j (Nat.sub j 1)) 2),j)
def jw:Nat->List (Nat × Nat)->Nat × Nat
 | _,[] => (0,0)
 | 0,a::_ => a
 | k+1,_::rest => jw k rest
def q38:Nat->List (Nat × Nat)->List (Nat × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::q38 k rest
def q203 (all1v code:Nat) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 if Nat.ble code 32 then
   zm (Nat.sub code 1) fun c =>
   zm (Nat.shiftRight c 1) fun i =>
   let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=jw i ws
   let wt:=if Nat.beq ta 3 then 2 else 0
   zm (Nat.xor a all1v) fun w =>
   let r:=q38 i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   zm (Nat.sub code 33) fun rem =>
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=jw i ws
   let (b,tb):=jw j ws
   let r:=q38 i (q38 j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     zm (Nat.land a b) fun w =>
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (w,wt)::r2
   else
     zm (Nat.lor a b) fun w =>
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (w,0)::r2
def q120 (all1v:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (Nat × Nat)
 | 0,_,_ => xs
 | d+1,s,j =>
   zm (q192 (PT s) j) fun e =>
   zm (Nat.land e 1023) fun code =>
   if Nat.beq code 0 then xs
   else zm (Nat.land (Nat.shiftRight e 10) 8191) fun pidx =>
     q203 all1v code (q120 all1v xs PT d (Nat.add s 1) pidx)
def Rgen (all1v cap:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat) (s j:Nat):List (Nat × Nat) :=
 q120 all1v xs PT (Nat.sub cap s) s j
def findAut1 (shTT salt:Nat) (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let ztt:=q72 shTT zs
 zm (q75 salt ztt) fun h =>
 zm (q85 NN FL HT s h) fun j =>
 !(Nat.beq j 999999)&&jk ztt (Rtt s j)
def findAut2 (shTT salt:Nat) (g0:List (Nat × Nat × Nat × Nat))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let ztt:=q72 shTT zs
 zm (q75 salt ztt) fun h0 =>
 zm (q85 NN FL HT s h0) fun j0 =>
 if !(Nat.beq j0 999999)&&jk ztt (Rtt s j0) then true
 else
   let ztt1:=wx g0 ztt
   zm (q75 salt ztt1) fun h1 =>
   zm (q85 NN FL HT s h1) fun j1 =>
   !(Nat.beq j1 999999)&&jk ztt1 (Rtt s j1)
def vm (salt:Nat) (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat):List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->Bool
 | [],ztt =>
   zm (q75 salt ztt) fun h =>
   zm (q85 NN FL HT s h) fun j =>
   !(Nat.beq j 999999)&&jk ztt (Rtt s j)
 | g::rest,ztt =>
   zm (q75 salt ztt) fun h =>
   zm (q85 NN FL HT s h) fun j =>
   if !(Nat.beq j 999999)&&jk ztt (Rtt s j) then true
   else vm salt Rtt NN FL HT s rest (wx g ztt)
def findAutPath (shTT salt:Nat) (path:List (List (Nat × Nat × Nat × Nat)))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 vm salt Rtt NN FL HT s path (q72 shTT zs)
def findAutGen (shTT salt:Nat) (gens:List (List (Nat × Nat × Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT PT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let zsc:=q186 gens (q72 shTT zs)
 zm (q75 salt zsc) fun h =>
 zm (q85 NN FL HT s h) fun j =>
 if Nat.beq j 999999 then false
 else
   zm (Nat.shiftRight (q192 (PT s) j) 23) fun aidx =>
   jk zsc (wx (aut aidx) (Rtt s j))
def bar (cfg:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (R:Nat->Nat->List (Nat × Nat)):Nat->Nat->Bool
 | 0,i => match R 0 i with
   | [(w,_)] => !(Nat.beq w cfg.goalv)
   | _ => true
 | s+1,i =>
   let ws:=R (Nat.add s 1) i
   !(scanAll cfg s ws fun zs =>
       !(findFn s zs)&&(Nat.beq s 0||scanInline cfg (Nat.sub s 1) zs))
def span (f:Nat->Bool):Nat->Nat->Bool
 | 0,_ => true
 | n+1,i => f i&&span f n (Nat.add i 1)
def q1 (n r:Nat):Fin n->Bool:=fun i => r.testBit i.val
def q146 {n:Nat} (x:Fin n->Bool):Nat :=
 (List.finRange n).foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0
lemma qp {m:Nat} (hm:m≠0):(1:Nat).testBit m=false:=by
 cases m with
 | zero => contradiction
 | succ k => simp [Nat.testBit_succ]
lemma z7 {x m:Nat} (h:x.testBit m=true) :
   (x / 2 ^ m) % 2=1:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 exact of_decide_eq_true h
lemma z5 {x m:Nat} (h:x.testBit m=false) :
   (x / 2 ^ m) % 2=0:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 have:=of_decide_eq_false h
 omega
lemma zg {x m:Nat} (h:x.testBit m=true) : 2 ^ m<=x:=by
 have h1:=z7 h
 have h2 : 1<=x / 2 ^ m:=by generalize x / 2 ^ m=q at h1 ⊢;omega
 have h3:=Nat.mul_le_mul_right (2 ^ m) h2
 have h4:=Nat.div_mul_le_self x (2 ^ m)
 omega
lemma vz {y m:Nat} (h:y.testBit m=false) :
   y % 2 ^ (m+1) < 2 ^ m:=by
 have h0:(y / 2 ^ m) % 2=0:=z5 h
 have h1:y % 2 ^ (m+1) / 2 ^ m=(y / 2 ^ m) % 2:=by
   rw [Nat.pow_succ,Nat.mod_mul_right_div_self]
 have h2:y % 2 ^ (m+1) / 2 ^ m=0:=by rw [h1,h0]
 exact (Nat.div_eq_zero_iff.1 h2).resolve_left (Nat.ne_of_gt (n2P m))
lemma vk {y m:Nat} (h:y.testBit m=false) (k:Nat) :
   (y+2 ^ m).testBit k=if k=m then true else y.testBit k:=by
 by_cases hkm:k=m
 . subst hkm
   have h0:=z5 h
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.add_div_right _ (n2P k)]
   simp;omega
 . simp only [hkm,↓reduceIte]
   by_cases hlt:k < m
   . have hdv : 2 ^ m=2 ^ k*2 ^ (m - k):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hlt)]
     have hge : 1<=m - k:=by omega
     have hev : 2 ^ (m - k) % 2=0:=by
       obtain ⟨q,hq⟩:=Nat.exists_eq_add_of_le' hge
       rw [hq,Nat.pow_succ];omega
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hdv,
         Nat.mul_comm (2 ^ k),Nat.add_mul_div_right _ _ (n2P k)]
     have:(y / 2 ^ k+2 ^ (m - k)) % 2=(y / 2 ^ k) % 2:=by omega
     rw [this]
   . have hge:m+1<=k:=by omega
     have hrem:y % 2 ^ (m+1)+2 ^ m < 2 ^ (m+1):=by
       have hltm:=vz h
       have hpw : 2 ^ (m+1)=2 ^ m*2:=Nat.pow_succ 2 m
       omega
     have hdiv1:(y+2 ^ m) / 2 ^ (m+1)=y / 2 ^ (m+1):=by
       have hd:y=2 ^ (m+1)*(y / 2 ^ (m+1))+y % 2 ^ (m+1) :=
         (Nat.div_add_mod y (2 ^ (m+1))).symm
       conv_lhs => rw [hd,nAA]
       rw [Nat.mul_add_div (n2P (m+1)),Nat.div_eq_of_lt hrem,nAZ]
     have hpow : 2 ^ k=2 ^ (m+1)*2 ^ (k - (m+1)):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' hge]
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hpow,
         ← Nat.div_div_eq_div_mul,← Nat.div_div_eq_div_mul,hdiv1]
lemma qs {y m:Nat} (h:y.testBit m=false) :
   y+2 ^ m=y^^^2 ^ m:=by
 apply nEQ;intro k
 rw [vk h,nTX,Nat.testBit_two_pow]
 by_cases hkm:k=m
 . subst hkm;simp [h]
 . simp [hkm,Ne.symm hkm]
lemma jl {n:Nat} (x:Fin n->Bool) (k:Nat) :
   (q146 x).testBit k=if h:k < n then x ⟨k,h⟩ else false:=by
 have hgen:∀ (l:List (Fin n)),l.Nodup ->
     (l.foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0).testBit k =
     if h:k < n then (if ⟨k,h⟩ ∈ l then x ⟨k,h⟩ else false) else false:=by
   intro l hnd
   induction l with
   | nil => simp
   | cons a t ih =>
     obtain ⟨hat,hndt⟩:=List.nodup_cons.1 hnd
     simp only [lFC]
     have iht:=ih hndt
     by_cases hxa:x a=true
     . simp only [hxa,↓reduceIte,nTO,Nat.testBit_shiftLeft,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . subst heq;simp [hxa]
         . have hne:k≠a.val:=fun e => heq (Fin.ext e)
           have h0:(decide (a.val<=k)&&(1:Nat).testBit (k - a.val))=false:=by
             cases hle:decide (a.val<=k)
             . simp
             . have hle':a.val<=k:=of_decide_eq_true hle
               simp [qp (by omega:k - a.val≠0)]
           simp [heq,h0]
       . have hne:a.val < k:=by omega
         simp [hk,qp (by omega:k - a.val≠0)]
     . simp only [hxa,bFT,↓reduceIte,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . rw [heq];simp [hat,hxa]
         . simp [heq]
       . simp [hk]
 have h:=hgen (List.finRange n) (List.nodup_finRange n)
 simpa [q146,List.mem_finRange] using h
lemma q178 {n:Nat} (x:Fin n->Bool):q146 x < 2 ^ n:=by
 apply Nat.lt_pow_two_of_testBit
 intro k hk
 rw [jl]
 simp [show ¬ k < n by omega]
lemma q57 {n:Nat} (x:Fin n->Bool):q1 n (q146 x)=x:=by
 funext i
 simp [q1,jl,i.isLt]
def encL {n:Nat} (rows:List Nat) (f:BFn n):Nat :=
 rows.foldr (fun r acc => acc*2+if f (q1 n r) then 1 else 0) 0
def encTT (n:Nat) (f:BFn n):Nat:=encL (List.range (2 ^ n)) f
lemma z8 {n:Nat} (rows:List Nat) (f:BFn n) (i:Nat) :
   (encL rows f).testBit i=match rows[i]? with | some r => f (q1 n r) | none => false:=by
 induction rows generalizing i with
 | nil => simp [encL]
 | cons r rest ih =>
   have hcons:encL (r::rest) f=encL rest f*2+if f (q1 n r) then 1 else 0:=rfl
   rw [hcons]
   cases i with
   | zero =>
     cases h:f (q1 n r) <;> simp [h,Nat.testBit_zero]
   | succ k =>
     rw [Nat.testBit_succ]
     have hd:(encL rest f*2+if f (q1 n r) then 1 else 0) / 2=encL rest f:=by
       cases h:f (q1 n r) <;> simp only [h,↓reduceIte,bFT] <;> omega
     rw [hd]
     exact ih k
lemma q39 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => false)=0:=by
 apply nEQ;intro i
 rw [z8];cases rows[i]? <;> simp
lemma q177 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => true)=2 ^ rows.length - 1:=by
 apply nEQ;intro i
 rw [z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]
lemma q160 {n:Nat} (rows:List Nat) (f:BFn n) :
   encL rows (invF f)=Nat.xor (encL rows f) (2 ^ rows.length - 1):=by
 apply nEQ;intro i
 rw [nXO,nTX,z8,z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi,invF]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]
lemma q143 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (meetF f g)=Nat.land (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLA,nTA,z8,z8,z8]
 cases rows[i]? <;> simp [meetF]
lemma q144 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (joinF f g)=Nat.lor (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLO,nTO,z8,z8,z8]
 cases rows[i]? <;> simp [joinF]
lemma vr {n:Nat} (f:BFn n) (r:Nat) :
   (encTT n f).testBit r=if r < 2 ^ n then f (q1 n r) else false:=by
 unfold encTT;rw [z8]
 by_cases hr:r < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]
lemma yc {n:Nat}:Function.Injective (encTT n):=by
 intro f g h
 funext x
 have h1:=congrArg (fun m => m.testBit (q146 x)) h
 rw [vr,vr] at h1
 simp only [q178 x,↓reduceIte,q57] at h1
 exact h1
lemma q116 {n:Nat} (pre:List Nat) (f:BFn n) :
   Nat.shiftRight (encL (pre++List.range (2 ^ n)) f) pre.length=encTT n f:=by
 apply nEQ;intro i
 change ((encL (pre++List.range (2 ^ n)) f) >>> pre.length).testBit i=(encTT n f).testBit i
 rw [Nat.shiftRight_eq_div_pow,Nat.testBit_div_two_pow,z8,vr]
 rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel]
 by_cases hi:i < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hi])];simp [hi]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hi]
lemma q89 {n:Nat} (pre:List Nat) :
   Function.Injective (encL (n:=n) (pre++List.range (2 ^ n))):=by
 intro f g h
 apply yc
 rw [← q116 pre f,← q116 pre g,h]
def yh {n:Nat} (i j:Fin n) (x:Fin n->Bool):Fin n->Bool :=
 fun k => x (if k=i then j else if k=j then i else k)
lemma q104 {n:Nat} (i j:Fin n) (x:Fin n->Bool) :
   yh i j (yh i j x)=x:=by
 funext k;unfold yh
 by_cases h1:k=i
 . rw [h1];by_cases h2:j=i <;> simp [h2]
 . by_cases h2:k=j
   . rw [h2];simp [Ne.symm h1]
   . simp [h1,h2]
def yu (i j r:Nat):Nat :=
 let bi:=r.testBit i
 let bj:=r.testBit j
 if bi==bj then r else Nat.xor r (Nat.lor (1 <<< i) (1 <<< j))
lemma q162 {n i j r:Nat} (hi:i < n) (hj:j < n) (hr:r < 2 ^ n) :
   yu i j r < 2 ^ n:=by
 unfold yu;dsimp only
 split
 . exact hr
 . apply Nat.lt_pow_two_of_testBit
   intro k hk
   rw [nXO,nTX,nLO,nTO,
       Nat.testBit_shiftLeft,Nat.testBit_shiftLeft]
   have hr0:r.testBit k=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hk))
   simp [hr0,qp (by omega:k - i≠0),qp (by omega:k - j≠0)]
lemma z9 {n i j r:Nat} (hi:i < n) (hj:j < n) :
   q1 n (yu i j r)=yh ⟨i,hi⟩ ⟨j,hj⟩ (q1 n r):=by
 funext k
 simp only [q1,yh,yu]
 by_cases heq:r.testBit i=r.testBit j
 . simp only [heq,beq_self_eq_true,↓reduceIte]
   by_cases hki:k=⟨i,hi⟩
   . rw [hki];simp [heq]
   . by_cases hkj:k=⟨j,hj⟩
     . rw [hkj];split <;> simp [heq]
     . simp [hki,hkj]
 . have hbeq:(r.testBit i==r.testBit j)=false:=beq_false_of_ne heq
   simp only [hbeq,bFT,↓reduceIte,nXO,nTX,nLO,
     nTO,Nat.testBit_shiftLeft]
   by_cases hki:k=⟨i,hi⟩
   . subst hki
     simp only [↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
     cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
   . by_cases hkj:k=⟨j,hj⟩
     . subst hkj
       simp only [hki,↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
       cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
     . have h1:k.val≠i:=fun e => hki (Fin.ext e)
       have h2:k.val≠j:=fun e => hkj (Fin.ext e)
       have hb:∀ m,k.val≠m->(decide (m<=k.val)&&(1:Nat).testBit (k.val - m))=false:=by
         intro m hne
         cases hle:decide (m<=k.val)
         . simp
         . have hle':m<=k.val:=of_decide_eq_true hle
           simp [qp (by omega:k.val - m≠0)]
       simp [hki,hkj,hb i h1,hb j h2]
def w9 (n i j:Nat):Nat × Nat × Nat × Nat :=
 let d:=2 ^ j - 2 ^ i
 let N:=2 ^ n
 let m01:=(List.range N).foldr (fun x acc => acc*2+if !(x.testBit i)&&x.testBit j then 1 else 0) 0
 let m10:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i&&!(x.testBit j) then 1 else 0) 0
 let mEq:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i==x.testBit j then 1 else 0) 0
 (d,m01,m10,mEq)
lemma jx (N:Nat) (P:Nat->Bool) (r:Nat) :
   ((List.range N).foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
   if r < N then P r else false:=by
 have hgen:∀ (l:List Nat) (r:Nat),
     (l.foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
     match l[r]? with | some x => P x | none => false:=by
   intro l
   induction l with
   | nil => intro r;simp
   | cons a t ih =>
     intro r;simp only [lFC]
     cases r with
     | zero => cases h:P a <;> simp [h,Nat.testBit_zero]
     | succ k =>
       rw [Nat.testBit_succ]
       have hd:((t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0)*2+if P a then 1 else 0) / 2
           = t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0:=by
         cases P a <;> simp only [↓reduceIte,bFT] <;> omega
       rw [hd];exact ih k
 rw [hgen]
 by_cases hr:r < N
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]
lemma j3 {n i j:Nat} (hij:i < j) (hjn:j < n) (g:BFn n) :
   q76 (w9 n i j) (encTT n g) =
     encTT n (fun x => g (yh ⟨i,by omega⟩ ⟨j,hjn⟩ x)):=by
 have hi:i < n:=by omega
 have hpow : 2 ^ i < 2 ^ j:=Nat.pow_lt_pow_right (by omega) hij
 have hsub_bit:∀ x m,x.testBit m=true->x - 2 ^ m+2 ^ m=x/\(x - 2 ^ m).testBit m=false:=by
   intro x m hm
   have hle : 2 ^ m<=x:=zg hm
   refine ⟨Nat.sub_add_cancel hle,?_⟩
   rw [Nat.testBit_eq_decide_div_mod_eq]
   have hd:(x - 2 ^ m) / 2 ^ m=x / 2 ^ m - 1:=by
     have h1:x=(x - 2 ^ m)+2 ^ m:=(Nat.sub_add_cancel hle).symm
     have h2:((x - 2 ^ m)+2 ^ m) / 2 ^ m=(x - 2 ^ m) / 2 ^ m+1 :=
       Nat.add_div_right (x - 2 ^ m) (n2P m)
     rw [← h1] at h2;rw [h2];simp
   have hm1:=z7 hm
   rw [hd];simp;generalize x / 2 ^ m=q at hm1 ⊢;omega
 have hsw_val:∀ (a b:Nat),a < b->b < n->∀ x < 2 ^ n,
     (x.testBit a=false->x.testBit b=true->x - (2 ^ b - 2 ^ a)=yu a b x) /\
     (x.testBit a=true->x.testBit b=false->x+(2 ^ b - 2 ^ a)=yu a b x):=by
   intro a b hab hbn x _
   have hpa : 2 ^ a < 2 ^ b:=Nat.pow_lt_pow_right (by omega) hab
   have hsh:∀ (m k:Nat),(decide (m<=k)&&(1:Nat).testBit (k - m))=decide (m=k):=by
     intro m k
     by_cases hmk:m=k
     . subst hmk;simp
     . cases hle:decide (m<=k)
       . simp [hmk]
       . have hle':m<=k:=of_decide_eq_true hle
         simp [hmk,qp (by omega:k - m≠0)]
   constructor
   . intro ha0 hb1
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x b hb1
     have hsub_a0:(x - 2 ^ b).testBit a=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit a) h2
       rw [nTX,Nat.testBit_two_pow,ha0] at htb
       have hba:b≠a:=by omega
       simp [hba] at htb;exact htb
     have h2:x - (2 ^ b - 2 ^ a)=(x - 2 ^ b)+2 ^ a:=by
       conv_lhs => rw [← hsub_eq]
       rw [Nat.add_sub_assoc (Nat.sub_le _ _),Nat.sub_sub_self (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ b)^^^2 ^ b:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ b)+2 ^ a=(x - 2 ^ b)^^^2 ^ a:=qs hsub_a0
     unfold yu;dsimp only
     simp only [ha0,hb1]
     change ((x - 2 ^ b)+2 ^ a).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
   . intro ha1 hb0
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x a ha1
     have hsub_b0:(x - 2 ^ a).testBit b=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit b) h2
       rw [nTX,Nat.testBit_two_pow,hb0] at htb
       have hab':a≠b:=by omega
       simp [hab'] at htb;exact htb
     have h2:x+(2 ^ b - 2 ^ a)=(x - 2 ^ a)+2 ^ b:=by
       conv_lhs => rw [← hsub_eq]
       rw [nAA,Nat.add_sub_cancel' (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ a)^^^2 ^ a:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ a)+2 ^ b=(x - 2 ^ a)^^^2 ^ b:=qs hsub_b0
     unfold yu;dsimp only
     simp only [ha1,hb0]
     change ((x - 2 ^ a)+2 ^ b).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
 have hodd_ji:(2 ^ (j - i) - 1) % 2=1:=by
   have hge : 1<=j - i:=by omega
   have hev : 2 ^ (j - i) % 2=0:=by
     obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge
     rw [hm,Nat.pow_succ];omega
   have hpos : 2<=2 ^ (j - i):=by
     have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge;simpa using this
   omega
 have hflip_add_i:∀ r,(r+(2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r+(2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i+(2 ^ (j - i) - 1):=by
     rw [hdv,Nat.mul_comm,Nat.add_mul_div_right _ _ (n2P i)]
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q;generalize 2 ^ (j - i) - 1=c at hodd_ji ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hflip_sub_i:∀ r,2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r hle
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r - (2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i - (2 ^ (j - i) - 1):=by
     have h2:r=(r - (2 ^ j - 2 ^ i))+(2 ^ j - 2 ^ i):=(Nat.sub_add_cancel hle).symm
     have h3:((r - (2 ^ j - 2 ^ i))+2 ^ i*(2 ^ (j - i) - 1)) / 2 ^ i
         = (r - (2 ^ j - 2 ^ i)) / 2 ^ i+(2 ^ (j - i) - 1):=by
       rw [Nat.mul_comm (2 ^ i),Nat.add_mul_div_right _ _ (n2P i)]
     rw [← hdv,← h2] at h3;rw [h3,Nat.add_sub_cancel]
   have hle_div : 2 ^ (j - i) - 1<=r / 2 ^ i:=by
     rw [hdv] at hle
     exact (Nat.le_div_iff_mul_le (n2P i)).2 (by rw [Nat.mul_comm];exact hle)
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q at hle_div ⊢;generalize 2 ^ (j - i) - 1=c at hodd_ji hle_div ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hshl_tb:∀ (x d k:Nat),(Nat.shiftLeft x d).testBit k=(decide (d<=k)&&x.testBit (k - d)):=by
   intro x d k
   change (x <<< d).testBit k=_
   rw [Nat.testBit_shiftLeft]
 apply nEQ
 intro r
 unfold q76 w9
 simp only [nLO,nLA,Nat.shiftRight_eq,Nat.shiftRight_eq_div_pow,
   nTO,nTA,Nat.testBit_div_two_pow,hshl_tb,
   jx,vr]
 by_cases hr:r < 2 ^ n
 . simp only [hr,↓reduceIte]
   have hsw:=hsw_val i j hij hjn r hr
   cases hri:r.testBit i <;> cases hrj:r.testBit j
   ·
     have h00_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h00_eq]
     have hmid:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hsub_j : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
       intro hle
       have h1:(r - (2 ^ j - 2 ^ i))+2 ^ j=r+2 ^ i:=by omega
       have hle_div : 1<=r / 2 ^ j:=by
         have hne0:r / 2 ^ j≠0:=by
           intro hz
           have hlt:r < 2 ^ j:=(Nat.div_eq_zero_iff.1 hz).resolve_left (Nat.ne_of_gt (n2P j))
           have hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ i:=by omega
           have hbi:(r - (2 ^ j - 2 ^ i)).testBit i=false:=Nat.testBit_lt_two_pow hlt2
           have:=hsub_i hle;rw [hbi] at this;cases this
         generalize r / 2 ^ j=q at hne0 ⊢;omega
       have hsub_div:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=r / 2 ^ j - 1:=by
         have h2:(r+2 ^ i) / 2 ^ j=r / 2 ^ j:=by
           have hrem:r % 2 ^ j+2 ^ i < 2 ^ j:=by
             have hm0:(r % 2 ^ j).testBit i=false:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
             have hlt1:r % 2 ^ j < 2 ^ j:=Nat.mod_lt r (n2P j)
             apply Nat.lt_pow_two_of_testBit;intro k hk
             rw [vk hm0]
             have hne:k≠i:=by omega
             simp only [hne,↓reduceIte]
             exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) hk))
           have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
           conv_lhs => rw [hdiv,nAA]
           rw [Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hrem,nAZ]
         have h3:((r - (2 ^ j - 2 ^ i))+2 ^ j) / 2 ^ j=(r - (2 ^ j - 2 ^ i)) / 2 ^ j+1 :=
           Nat.add_div_right _ (n2P j)
         rw [h1,h2] at h3;omega
       have hrj0:=z5 hrj
       rw [Nat.testBit_eq_decide_div_mod_eq,hsub_div];simp
       generalize r / 2 ^ j=q at hle_div hrj0 ⊢;omega
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_j hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
   ·
     have hle_j : 2 ^ j<=r:=zg hrj
     have hle : 2 ^ j - 2 ^ i<=r:=le_trans (Nat.sub_le _ _) hle_j
     have hsw_eq:r - (2 ^ j - 2 ^ i)=yu i j r:=hsw.1 hri hrj
     have hsw_lt:r - (2 ^ j - 2 ^ i) < 2 ^ n:=by omega
     have hsw_i:(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r - (2 ^ j - 2 ^ i)).testBit j=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hmid_i:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_i]
     rw [hterm1]
     simp [hle,hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have hsw_eq:r+(2 ^ j - 2 ^ i)=yu i j r:=hsw.2 hri hrj
     have hsw_lt:r+(2 ^ j - 2 ^ i) < 2 ^ n:=by rw [hsw_eq];exact q162 hi hjn hr
     have hsw_i:(r+(2 ^ j - 2 ^ i)).testBit i=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r+(2 ^ j - 2 ^ i)).testBit j=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm2]
     simp [hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have h11_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h11_eq]
     have hmid_j:(r+(2 ^ j - 2 ^ i)).testBit j=false:=by
       have hle_i : 2 ^ i<=r:=zg hri
       have hsub_rem:(r - 2 ^ i) / 2 ^ j=r / 2 ^ j:=by
         have hm1:(r % 2 ^ j).testBit i=true:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
         have hmod_i : 2 ^ i<=r % 2 ^ j:=zg hm1
         have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
         have hsub:r - 2 ^ i=2 ^ j*(r / 2 ^ j)+(r % 2 ^ j - 2 ^ i):=by omega
         have hlt:r % 2 ^ j - 2 ^ i < 2 ^ j:=lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt r (n2P j))
         rw [hsub,Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hlt,nAZ]
       have h1:r+(2 ^ j - 2 ^ i)=(r - 2 ^ i)+2 ^ j:=by omega
       rw [Nat.testBit_eq_decide_div_mod_eq,h1,Nat.add_div_right _ (n2P j),hsub_rem]
       have hr1:=z7 hrj
       simp;omega
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_j]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
 ·
   have hge1 : ¬ (r+(2 ^ j - 2 ^ i) < 2 ^ n):=by omega
   simp only [hr,hge1,↓reduceIte,Bool.and_false,Bool.false_or]
   by_cases hle : 2 ^ j - 2 ^ i<=r
   . by_cases hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ n
     . have hsub_j:(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
         have hge_q : 2 ^ (n - j) - 1<=(r - (2 ^ j - 2 ^ i)) / 2 ^ j:=by
           have h1 : 2 ^ j*(2 ^ (n - j) - 1)=2 ^ n - 2 ^ j:=by
             rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           have h2 : 2 ^ n - 2 ^ j<=r - (2 ^ j - 2 ^ i) :=
             le_trans (Nat.sub_le_sub_left (Nat.sub_le _ _) _) (Nat.sub_le_sub_right (by omega : 2 ^ n<=r) _)
           exact (Nat.le_div_iff_mul_le (n2P j)).2 (by rw [Nat.mul_comm,h1];exact h2)
         have hlt_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j < 2 ^ (n - j):=by
           have h1 : 2 ^ n=2 ^ j*2 ^ (n - j):=by
             rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           exact (Nat.div_lt_iff_lt_mul (n2P j)).2 (by rw [Nat.mul_comm,← h1];exact hlt2)
         have heq_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=2 ^ (n - j) - 1:=by omega
         rw [Nat.testBit_eq_decide_div_mod_eq,heq_q]
         have hge1' : 1<=n - j:=by omega
         have hev : 2 ^ (n - j) % 2=0:=by
           obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge1'
           rw [hm,Nat.pow_succ];omega
         have hpos : 2<=2 ^ (n - j):=by
           have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge1';simpa using this
         simp;omega
       simp [hle,hlt2,hsub_j]
     . simp [hle,hlt2]
   . simp [hle]
def q163 (n:Nat) (ps:List (Nat × Nat)):List (Nat × Nat × Nat × Nat) :=
 ps.map fun p => w9 n p.1 p.2
def kq (n:Nat) (ps:List (Nat × Nat)):Bool :=
 ps.all fun p => decide (p.1 < p.2)&&decide (p.2 < n)
def zc {n:Nat}:List (Nat × Nat)->(Fin n->Bool)->(Fin n->Bool)
 | [],x => x
 | (i,j)::rest,x =>
   if h:i < n/\j < n then yh ⟨i,h.1⟩ ⟨j,h.2⟩ (zc rest x)
   else zc rest x
lemma wv {n:Nat} (ps:List (Nat × Nat)) (x:Fin n->Bool) :
   zc ps.reverse (zc ps x)=x:=by
 have hcomp:∀ (a b:List (Nat × Nat)) (y:Fin n->Bool),
     zc (a++b) y=zc a (zc b y):=by
   intro a;induction a with
   | nil => intro b y;rfl
   | cons p t ih =>
     intro b y;rcases p with ⟨i,j⟩
     simp only [lCA,zc];split <;> rw [ih]
 induction ps generalizing x with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨i,j⟩
   simp only [lRC,hcomp,zc]
   split
   . rename_i h
     rw [q104,ih]
   . exact ih x
lemma jm {n:Nat} (ps:List (Nat × Nat)) (hv:kq n ps=true) (g:BFn n) :
   ym (q163 n ps) (encTT n g)=encTT n (fun x => g (zc ps x)):=by
 induction ps generalizing g with
 | nil => rfl
 | cons p rest ih =>
   rcases p with ⟨i,j⟩
   simp only [kq,List.all_cons,bAT,decide_eq_true_eq] at hv
   obtain ⟨⟨hij,hjn⟩,hrest⟩:=hv
   change ym (w9 n i j::q163 n rest) (encTT n g)=_
   simp only [ym]
   rw [j3 hij hjn g,ih hrest]
   congr 1;funext x
   have hlt:i < n/\j < n:=by omega
   simp only [zc]
   split
   . rfl
   . contradiction
def vh {n:Nat} (f:BFn n) (sws:List (Nat × Nat × Nat × Nat)):Prop :=
 ∃ π:(Fin n->Bool)->(Fin n->Bool),
   Function.Bijective π/\(∀ x,f (π x)=f x) /\
   ∀ g:BFn n,ym sws (encTT n g)=encTT n (fun x => g (π x))
lemma kw {n:Nat} (f:BFn n) (ps:List (Nat × Nat))
   (hv:kq n ps=true)
   (hfix:ym (q163 n ps) (encTT n f)=encTT n f) :
   vh f (q163 n ps):=by
 refine ⟨zc ps,?_,?_,fun g => jm ps hv g⟩
 . constructor
   . intro x y h
     have:=congrArg (zc ps.reverse) h
     simpa [wv] using this
   . intro y
     refine ⟨zc ps.reverse y,?_⟩
     have:=wv ps.reverse y
     simpa using this
 . intro x
   rw [jm ps hv f] at hfix
   exact congrFun (yc hfix) x
lemma q138 {n:Nat} (f:BFn n):vh f [] :=
 ⟨id,Function.bijective_id,fun _ => rfl,fun _ => rfl⟩
lemma wp {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (π:(Fin n->Bool)->(Fin n->Bool)) (hbij:Function.Bijective π) (hfix:∀ x,f (π x)=f x)
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws) :
   TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s
     (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 let φ:BFn n->BFn n:=fun g x => g (π x)
 have hφ:Function.Injective φ:=by
   intro g1 g2 heq;funext y
   obtain ⟨x,rfl⟩:=hbij.2 y
   exact congrFun heq x
 exact @TagRun.map (BFn n) (BFn n) φ hφ
   invF meetF joinF (fun _ => false) (fun _ => true) f
   invF meetF joinF (fun _ => false) (fun _ => true) f
   rfl rfl (funext hfix) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) s ws h
def z6 (x i:Nat):Nat:=(x / 64 ^ i) % 64
lemma q185 (i:Nat) : 64 ^ i=2 ^ (6*i):=by
 rw [show (64:Nat)=2 ^ 6 by decide,← Nat.pow_mul]
lemma qo (x i k:Nat) :
   (z6 x i).testBit k=if k < 6 then x.testBit (6*i+k) else false:=by
 unfold z6
 rw [q185,show (64:Nat)=2 ^ 6 by decide,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
 by_cases hk:k < 6
 . simp [hk,nAC]
 . simp [hk]
lemma wg {x y:Nat} (h:∀ i,z6 x i=z6 y i):x=y:=by
 apply nEQ;intro k
 have h1:=congrArg (fun z => z.testBit (k % 6)) (h (k / 6))
 have hm:k % 6 < 6:=Nat.mod_lt k (by decide)
 rw [qo,qo] at h1
 simp only [hm,↓reduceIte,Nat.div_add_mod] at h1
 exact h1
lemma z1 (x i:Nat):z6 (x / 64) i=z6 x (i+1):=by
 unfold z6
 rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (64 ^ i) 64]
lemma q24:∀ {x y:Nat},(∀ i,z6 y i<=z6 x i)->y<=x:=by
 intro x y h
 induction hn:x+y using Nat.strong_induction_on generalizing x y with
 | _ n ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   by_cases hq:x / 64+y / 64 < x+y
   . have hdiv:y / 64<=x / 64 :=
       ih (x / 64+y / 64) (by omega) (fun i => by rw [z1,z1];exact h (i+1)) rfl
     omega
   . omega
lemma q25 {x y:Nat} (h:∀ j,z6 x j+z6 y j < 64) (i:Nat) :
   z6 (x+y) i=z6 x i+z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   have hdiv:(x+y) / 64=x / 64+y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))
lemma q188 {x y:Nat} (h:∀ j,z6 y j<=z6 x j) (i:Nat) :
   z6 (x - y) i=z6 x i - z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   have hdiv:(x - y) / 64=x / 64 - y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))
lemma v9 (x y i:Nat):z6 (Nat.land x y) i=Nat.land (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTA]
lemma wb (x y i:Nat):z6 (Nat.lor x y) i=Nat.lor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLO,nLO,nTO,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTO]
lemma q110 (x y i:Nat):z6 (Nat.xor x y) i=Nat.xor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nXO,nXO,nTX,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTX]
def qe (m val:Nat):Nat :=
 match m with
 | 0 => 0
 | m'+1 => val+64*qe m' val
lemma v0 (m val i:Nat) (hv:val < 64) :
   z6 (qe m val) i=if i < m then val else 0:=by
 induction m generalizing i with
 | zero => simp [qe,z6]
 | succ m ih =>
   cases i with
   | zero => simp only [qe,z6,Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,↓reduceIte];omega
   | succ k =>
     rw [← z1]
     have hd:qe (m+1) val / 64=qe m val:=by simp only [qe];omega
     rw [hd,ih k]
     by_cases h:k < m <;> simp [h,show k+1 < m+1 ↔ k < m by omega]
def v6 (a b c d e f:Bool):Nat :=
 let nd:=!d;let ne:=!e;let nf:=!f
 (if nd&&b then 1 else 0)+(if nd&&c then 1 else 0) +
 (if a&&ne then 1 else 0)+(if a&&nf then 1 else 0) -
 (if (a&&nd)&&((b||c)&&(ne||nf)) then 1 else 0)
def zq (a b c d e f:Bool):Nat :=
 max (v6 a b c d e f) (v6 (!a) (!b) (!c) (!d) (!e) (!f))
lemma q122:v6 true true true false false false=3:=by decide
lemma yr:∀ a b c d e f:Bool,v6 a b c d e f<=3:=by decide
lemma q52:∀ a b c d e f:Bool,zq a b c d e f<=3:=by decide
lemma k7:∀ a b c d e f:Bool,v6 a b c d e f<=zq a b c d e f:=by decide
lemma jp:∀ a b c d e f:Bool,zq (!a) (!b) (!c) (!d) (!e) (!f)=zq a b c d e f:=by decide
lemma w4:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma kl:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma q14 (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=w4 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=kl (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_or]
 omega
lemma je (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=kl a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=w4 (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_and]
 omega
lemma wc (w s m i:Nat) :
   z6 (Nat.land (Nat.shiftRight w s) (qe m 1)) i =
     if i < m then (if w.testBit (6*i+s) then 1 else 0) else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (w >>> s).testBit (6*i)=_
     rw [nTS,nAC s (6*i)]
     cases h:w.testBit (6*i+s) <;> simp [h]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     cases w.testBit (6*i+s) <;> simp [qp (by omega:k'+1≠0)]
 . simp [hi,nLA]
lemma yy (m w0 i:Nat) :
   z6 (qi (qe m 1) w0) i =
     if i < m then
       v6 (w0.testBit (6*i)) (w0.testBit (6*i+1)) (w0.testBit (6*i+2))
               (w0.testBit (6*i+3)) (w0.testBit (6*i+4)) (w0.testBit (6*i+5))
     else 0:=by
 unfold qi
 simp only [v5]
 have hbit:∀ s j,z6 (Nat.land (Nat.shiftRight w0 s) (qe m 1)) j =
     if j < m then (if w0.testBit (6*j+s) then 1 else 0) else 0:=fun s j => wc w0 s m j
 have hbit0:∀ j,z6 (Nat.land w0 (qe m 1)) j =
     if j < m then (if w0.testBit (6*j) then 1 else 0) else 0:=fun j => by
   have:=hbit 0 j;simpa using this
 have hxor:∀ s j,z6 (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1))) j =
     if j < m then (if !(w0.testBit (6*j+s)) then 1 else 0) else 0:=by
   intro s j
   rw [q110,v0 m 1 j (by decide),hbit s j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte];cases w0.testBit (6*j+s) <;> decide
   . simp [hj]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set nd:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 3) (qe m 1))
 set ne:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 4) (qe m 1))
 set nf:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 5) (qe m 1))
 have h_and_b:∀ bx by_:Bool,
     Nat.land (if bx then 1 else 0) (if by_ then 1 else 0)=if bx&&by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have h_or_b:∀ bx by_:Bool,
     Nat.lor (if bx then 1 else 0) (if by_ then 1 else 0)=if bx||by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have hL:∀ j,z6 (Nat.land nd b) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+1) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 1 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL2:∀ j,z6 (Nat.land nd c) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+2) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 2 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL3:∀ j,z6 (Nat.land a ne) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+4)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 4 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL4:∀ j,z6 (Nat.land a nf) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+5)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 5 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hSub:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j =
     if j < m then (if (w0.testBit (6*j)&&!(w0.testBit (6*j+3))) &&
       ((w0.testBit (6*j+1)||w0.testBit (6*j+2)) &&
        (!(w0.testBit (6*j+4))||!(w0.testBit (6*j+5)))) then 1 else 0) else 0:=by
   intro j
   rw [v9 (Nat.land a nd),v9 a nd,v9 (Nat.lor b c),wb b c,wb ne nf,
       hbit0 j,hxor 3 j,hbit 1 j,hbit 2 j,hxor 4 j,hxor 5 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,h_and_b,h_or_b]
   . simp [hj]
 have hSum1:∀ j,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j:=fun j =>
   q25 (fun l => by rw [hL l,hL2 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSum2:∀ j,z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) j =
     z6 (Nat.land a ne) j+z6 (Nat.land a nf) j:=fun j =>
   q25 (fun l => by rw [hL3 l,hL4 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSumAll:∀ j,z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j+(z6 (Nat.land a ne) j+z6 (Nat.land a nf) j):=by
   intro j
   have hlt:∀ l,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) l+z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) l < 64:=by
     intro l;rw [hSum1 l,hSum2 l,hL l,hL2 l,hL3 l,hL4 l]
     by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> split <;> split <;> omega
   change z6 (_+_) j=_
   rw [q25 hlt j,hSum1 j,hSum2 j]
 have hSubLe:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j <=
     z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j:=by
   intro j;rw [hSumAll j,hSub j,hL j,hL2 j,hL3 j,hL4 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte]
     cases w0.testBit (6*j) <;> cases w0.testBit (6*j+1) <;> cases w0.testBit (6*j+2) <;>
       cases w0.testBit (6*j+3) <;> cases w0.testBit (6*j+4) <;> cases w0.testBit (6*j+5) <;> decide
   . simp [hj]
 change z6 (_ - _) i=_
 rw [q188 hSubLe i,hSumAll i,hSub i,hL i,hL2 i,hL3 i,hL4 i]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte,v6]
   omega
 . simp [hi]
lemma q51:∀ v1 v2:Nat,v1<=3->v2<=3 ->
   let u:=Nat.lor v1 v2
   let hi:=Nat.land u 2
   Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                       (Nat.land (Nat.land u 1) (Nat.xor 1 (Nat.shiftRight hi 1))))=max v1 v2:=by
 intro v1 v2 h1 h2
 interval_cases v1 <;> interval_cases v2 <;> decide
lemma ya {v:Nat} (hv:∀ j,z6 v j<=3) (i:Nat) :
   z6 (Nat.land v (Nat.shiftRight v 1)) i=Nat.land (z6 v i) (Nat.shiftRight (z6 v i) 1):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo]
 by_cases hk:k < 6
 . simp only [hk,↓reduceIte,nTA]
   change (v.testBit (6*i+k)&&(v >>> 1).testBit (6*i+k)) =
     (v.testBit (6*i+k)&&((z6 v i) >>> 1).testBit k)
   rw [nTS,nTS,qo]
   by_cases hk5:k < 5
   . have hk1 : 1+k < 6:=by omega
     simp only [hk1,↓reduceIte]
     have : 1+(6*i+k)=6*i+(1+k):=by omega
     rw [this]
   . have hk_eq:k=5:=by omega
     subst hk_eq
     have hvi:z6 v i < 4:=by have:=hv i;omega
     have htb5:(z6 v i).testBit 5=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hvi (by decide))
     rw [qo] at htb5
     simp only [show 5 < 6 by decide,↓reduceIte] at htb5
     simp [htb5]
 . simp [hk]
lemma jv {hi:Nat} (hhi:∀ j,z6 hi j=0\/z6 hi j=2) (i:Nat) :
   z6 (Nat.land (Nat.shiftRight hi 1) (qe m 1)) i =
     if i < m then Nat.shiftRight (z6 hi i) 1 else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (hi >>> 1).testBit (6*i)=((z6 hi i) >>> 1).testBit 0
     rw [nTS,nTS,qo]
     simp [nAC]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     rcases hhi i with h0 | h2
     . rw [h0];simp
     . rw [h2];change false=((2 >>> 1:Nat).testBit (k'+1));simp [qp (by omega:k'+1≠0)]
 . simp [hm,nLA]
lemma kh (sh1 m w i:Nat) :
   z6 (yg sh1 (qe m 1) (qe m 2) w) i =
     if i < m then
       zq (w.testBit (sh1+6*i)) (w.testBit (sh1+6*i+1)) (w.testBit (sh1+6*i+2))
               (w.testBit (sh1+6*i+3)) (w.testBit (sh1+6*i+4)) (w.testBit (sh1+6*i+5))
     else 0:=by
 unfold yg
 simp only [v5]
 set w0:=Nat.shiftRight w sh1
 have hw0:∀ k,w0.testBit k=w.testBit (sh1+k):=fun k => by
   change (w >>> sh1).testBit k=_;rw [nTS,nAC]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set d:=Nat.land (Nat.shiftRight w0 3) (qe m 1)
 set e:=Nat.land (Nat.shiftRight w0 4) (qe m 1)
 set f:=Nat.land (Nat.shiftRight w0 5) (qe m 1)
 set nd:=Nat.xor (qe m 1) d
 set ne:=Nat.xor (qe m 1) e
 set nf:=Nat.xor (qe m 1) f
 set na:=Nat.xor (qe m 1) a
 set nb:=Nat.xor (qe m 1) b
 set nc:=Nat.xor (qe m 1) c
 set v1:=Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                   (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
 set v2:=Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                   (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))
 have hv1_eq:v1=qi (qe m 1) w0:=by
   unfold qi;simp only [v5];rfl
 have hv1:∀ j,z6 v1 j=if j < m then
     v6 (w0.testBit (6*j)) (w0.testBit (6*j+1)) (w0.testBit (6*j+2))
             (w0.testBit (6*j+3)) (w0.testBit (6*j+4)) (w0.testBit (6*j+5)) else 0:=by
   intro j;rw [hv1_eq,yy]
 have hv2_eq:v2=qi (qe m 1) (Nat.xor w0 (2 ^ (6*m) - 1)):=by
   have hbit_inv:∀ s,s < 6->Nat.land (Nat.shiftRight (Nat.xor w0 (2 ^ (6*m) - 1)) s) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1)):=by
     intro s hs
     apply wg;intro j
     rw [wc,q110,v0 m 1 j (by decide),wc]
     by_cases hj:j < m
     . have hlt : 6*j+s < 6*m:=by omega
       simp only [hj,↓reduceIte,nXO,nTX,nTB,hlt,decide_true]
       cases w0.testBit (6*j+s) <;> decide
     . simp [hj]
   have hbit_inv0:Nat.land (Nat.xor w0 (2 ^ (6*m) - 1)) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land w0 (qe m 1)):=by
     have:=hbit_inv 0 (by decide);simpa using this
   have hxor_inv:∀ x,Nat.xor (qe m 1) (Nat.xor (qe m 1) x)=x:=by
     intro x;apply nEQ;intro k
     rw [nXO,nXO,nTX,nTX]
     cases (qe m 1).testBit k <;> cases x.testBit k <;> decide
   unfold qi;simp only [v5]
   rw [hbit_inv0,hbit_inv 1 (by decide),hbit_inv 2 (by decide),
       hbit_inv 3 (by decide),hbit_inv 4 (by decide),hbit_inv 5 (by decide),
       hxor_inv,hxor_inv,hxor_inv]
 have hv2:∀ j,z6 v2 j=if j < m then
     v6 (!(w0.testBit (6*j))) (!(w0.testBit (6*j+1))) (!(w0.testBit (6*j+2)))
             (!(w0.testBit (6*j+3))) (!(w0.testBit (6*j+4))) (!(w0.testBit (6*j+5))) else 0:=by
   intro j;rw [hv2_eq,yy]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,nXO,nTX,nTB]
     simp only [show 6*j < 6*m by omega,show 6*j+1 < 6*m by omega,
       show 6*j+2 < 6*m by omega,show 6*j+3 < 6*m by omega,
       show 6*j+4 < 6*m by omega,show 6*j+5 < 6*m by omega,
       decide_true,bBT]
   . simp [hj]
 have hv1_le3:∀ j,z6 v1 j<=3:=fun j => by
   rw [hv1 j];split;exact yr _ _ _ _ _ _;omega
 have hv2_le3:∀ j,z6 v2 j<=3:=fun j => by
   rw [hv2 j];split;exact yr _ _ _ _ _ _;omega
 set u:=Nat.lor v1 v2
 set hi:=Nat.land u (qe m 2)
 have hhi_lane:∀ j,z6 hi j=if j < m then Nat.land (Nat.lor (z6 v1 j) (z6 v2 j)) 2 else 0:=by
   intro j;rw [v9,wb,v0 m 2 j (by decide)]
   by_cases hj:j < m <;> simp [hj,nLA]
 have hhi02:∀ j,z6 hi j=0\/z6 hi j=2:=by
   intro j;rw [hhi_lane j]
   split
   . have h1:=hv1_le3 j;have h2:=hv2_le3 j
     generalize z6 v1 j=x at h1;generalize z6 v2 j=y at h2
     interval_cases x <;> interval_cases y <;> decide
   . left;rfl
 have hlast:z6 (Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1))) i =
     if i < m then Nat.land (Nat.land (Nat.lor (z6 v1 i) (z6 v2 i)) 1) (Nat.xor 1 (Nat.shiftRight (z6 hi i) 1)) else 0:=by
   have hrew:Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1)) =
       Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight hi 1) (qe m 1))):=by
     apply nEQ;intro k
     simp only [nLA,nXO,nTA,nTX]
     cases (qe m 1).testBit k <;> simp
   rw [hrew,v9,v9,wb,q110,v0 m 1 i (by decide),
       jv (m:=m) hhi02 i]
   by_cases hm:i < m <;> simp [hm,nLA]
 rw [wb,wb,wb,ya hv1_le3 i,
     ya hv2_le3 i,hlast,hhi_lane i]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   have hmain:=q51 (z6 v1 i) (z6 v2 i) (hv1_le3 i) (hv2_le3 i)
   simp only at hmain
   rw [hmain,hv1 i,hv2 i]
   simp only [hm,↓reduceIte,hw0,zq]
   have ha1:sh1+(6*i+1)=sh1+6*i+1:=by omega
   have ha2:sh1+(6*i+2)=sh1+6*i+2:=by omega
   have ha3:sh1+(6*i+3)=sh1+6*i+3:=by omega
   have ha4:sh1+(6*i+4)=sh1+6*i+4:=by omega
   have ha5:sh1+(6*i+5)=sh1+6*i+5:=by omega
   rw [ha1,ha2,ha3,ha4,ha5]
 . simp only [hm,↓reduceIte,hv1 i,hv2 i];decide
lemma q47 {α:Type} (f : α->Nat) (m:Nat)
   (hf:∀ x i,z6 (f x) i<=(if i < m then 3 else 0))
   (xs:List α) (hlen:xs.length<=11) (i:Nat) :
   z6 (xs.foldr (fun x acc => Nat.add (f x) acc) 0) i=(xs.map fun x => z6 (f x) i).sum /\
   (xs.map fun x => z6 (f x) i).sum<=if i < m then 3*xs.length else 0:=by
 induction xs generalizing i with
 | nil => simp [z6]
 | cons a t ih =>
   simp only [lLC] at hlen
   have ih_all:∀ j,z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j =
       (t.map fun x => z6 (f x) j).sum /\
       (t.map fun x => z6 (f x) j).sum<=if j < m then 3*t.length else 0 :=
     fun j => ih (by omega) j
   have hlt:∀ j,z6 (f a) j+z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j < 64:=by
     intro j
     have h1:=hf a j
     have ⟨h2,h3⟩:=ih_all j
     rw [h2]
     by_cases hj:j < m <;> simp only [hj,↓reduceIte] at h1 h3 <;> omega
   simp only [lFC,lMC,List.sum_cons,lLC]
   have hadd:=q25 hlt i
   have hfa:=hf a i
   have ⟨h2,h3⟩:=ih_all i
   refine ⟨?_,?_⟩
   . change z6 (_+_) i=_;rw [hadd,h2]
   . by_cases hi:i < m <;> simp only [hi,↓reduceIte] at hfa h3 ⊢ <;> omega
lemma ky (S m:Nat)
   (hS_bound:∀ i,z6 S i<=if i < m then 33 else 0)
   (hS_ge3:∀ i < m,3<=z6 S i) :
   Nat.beq (Nat.land (Nat.add S (qe m 29)) (qe m 32)) (qe m 32)=true:=by
 rw [Nat.beq_eq]
 apply wg;intro i
 have hlt:∀ j,z6 S j+z6 (qe m 29) j < 64:=by
   intro j;rw [v0 m 29 j (by decide)]
   have hb:=hS_bound j
   by_cases hj:j < m <;> simp only [hj,↓reduceIte] at hb ⊢ <;> omega
 rw [v9]
 change Nat.land (z6 (S+qe m 29) i) (z6 (qe m 32) i)=z6 (qe m 32) i
 rw [q25 hlt i,v0 m 29 i (by decide),v0 m 32 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   have hb:=hS_bound i;simp only [hi,↓reduceIte] at hb
   have hge:=hS_ge3 i hi
   have h1 : 32<=z6 S i+29:=by omega
   have h2:z6 S i+29 < 64:=by omega
   generalize z6 S i+29=v at h1 h2
   interval_cases v <;> decide
 . simp [hi,nLA]
def j5 (rp:Nat):Nat->Nat->List Nat
 | 0,_ => []
 | m+1,idx => Nat.land (Nat.shiftRight rp (Nat.mul 7 idx)) 127::j5 rp m (Nat.add idx 1)
lemma q32 (rp m idx:Nat):(j5 rp m idx).length=m:=by
 induction m generalizing idx with
 | zero => rfl
 | succ m ih => simp [j5,ih]
def q106 (rp shTT:Nat):List Nat:=j5 rp shTT 0
def allRows (n rp shTT:Nat):List Nat:=q106 rp shTT++List.range (2 ^ n)
lemma jj (rp shTT:Nat):(q106 rp shTT).length=shTT :=
 q32 rp shTT 0
lemma zl (n rp shTT:Nat):(allRows n rp shTT).length=shTT+2 ^ n:=by
 simp [allRows,jj]
structure CfgOk (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Prop where
 sh0_eq:c.sh0=2*c.k
 sh0_le:c.sh0<=c.sh1
 sh1_le:c.sh1<=c.shTT
 p0_dvd:(c.sh1 - c.sh0) % 6=0
 p1_dvd:(c.shTT - c.sh1) % 6=0
 all1v_eq:c.all1v=2 ^ (c.shTT+2 ^ n) - 1
 goalv_eq:c.goalv=encL (allRows n rp c.shTT) f
 lok_eq:c.lok=2 ^ c.k - 1
 m0all_eq:c.m0all=2 ^ (6*((c.sh1 - c.sh0) / 6)) - 1
 m0_eq:c.m0=qe ((c.sh1 - c.sh0) / 6) 1
 a29_0_eq:c.a29_0=qe ((c.sh1 - c.sh0) / 6) 29
 b5_0_eq:c.b5_0=qe ((c.sh1 - c.sh0) / 6) 32
 m1_eq:c.m1=qe ((c.shTT - c.sh1) / 6) 1
 m12_eq:c.m12=qe ((c.shTT - c.sh1) / 6) 2
 a29_1_eq:c.a29_1=qe ((c.shTT - c.sh1) / 6) 29
 b5_1_eq:c.b5_1=qe ((c.shTT - c.sh1) / 6) 32
 cov_ok:∀ i < c.k,
   f (q1 n ((allRows n rp c.shTT).getD i 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.k+i) 0))=true
 p0_ok:∀ i < (c.sh1 - c.sh0) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+5) 0))=false
 p1_ok:∀ i < (c.shTT - c.sh1) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+5) 0))=false
def w3 (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Bool :=
 let np0:=(c.sh1 - c.sh0) / 6
 let np1:=(c.shTT - c.sh1) / 6
 Nat.beq c.sh0 (2*c.k) &&
 Nat.ble c.sh0 c.sh1 &&
 Nat.ble c.sh1 c.shTT &&
 Nat.beq ((c.sh1 - c.sh0) % 6) 0 &&
 Nat.beq ((c.shTT - c.sh1) % 6) 0 &&
 Nat.beq c.all1v (2 ^ (c.shTT+2 ^ n) - 1) &&
 Nat.beq c.goalv (encL (allRows n rp c.shTT) f) &&
 Nat.beq c.lok (2 ^ c.k - 1) &&
 Nat.beq c.m0all (2 ^ (6*np0) - 1) &&
 Nat.beq c.m0 (qe np0 1) &&
 Nat.beq c.a29_0 (qe np0 29) &&
 Nat.beq c.b5_0 (qe np0 32) &&
 Nat.beq c.m1 (qe np1 1) &&
 Nat.beq c.m12 (qe np1 2) &&
 Nat.beq c.a29_1 (qe np1 29) &&
 Nat.beq c.b5_1 (qe np1 32) &&
 Nat.beq (Nat.land c.goalv c.lok) 0 &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.k) c.lok) c.lok &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh0) c.m0all) (qe np0 7) &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh1) (2 ^ (6*np1) - 1)) (qe np1 7)
lemma qm {n:Nat} (rows:List Nat) (f:BFn n) {idx:Nat} (h:idx < rows.length) :
   (encL rows f).testBit idx=f (q1 n (rows.getD idx 0)):=by
 rw [z8,List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]
lemma jn (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg)
   (h:w3 n f rp c=true):CfgOk n f rp c:=by
 unfold w3 at h
 simp only [bAT,Nat.beq_eq,Nat.ble_eq] at h
 rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh0,h01⟩,h1t⟩,hp0d⟩,hp1d⟩,hall1⟩,hgoal⟩,hlok⟩,hm0all⟩,
   hm0⟩,ha29_0⟩,hb5_0⟩,hm1⟩,hm12⟩,ha29_1⟩,hb5_1⟩,hcov0⟩,hcov1⟩,hp0m⟩,hp1m⟩
 have hlen:(allRows n rp c.shTT).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hbit_goal:∀ idx < c.shTT,c.goalv.testBit idx=f (q1 n ((allRows n rp c.shTT).getD idx 0)):=by
   intro idx hidx
   rw [hgoal,qm _ _ (by rw [hlen];exact Nat.lt_add_right (2 ^ n) hidx)]
 have hlane7:∀ (sh m:Nat),sh+6*m<=c.shTT ->
     Nat.land (Nat.shiftRight c.goalv sh) (2 ^ (6*m) - 1)=qe m 7 ->
     ∀ i < m,
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+1) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+2) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+3) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+4) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+5) 0))=false:=by
   intro sh m hbound heq i hi
   have htb:∀ off < 6,f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+off) 0))=(7:Nat).testBit off:=by
     intro off hoff
     have h1:=congrArg (fun z => z6 z i) heq
     rw [v0 m 7 i (by decide)] at h1
     simp only [hi,↓reduceIte] at h1
     have h2:=congrArg (fun z => z.testBit off) h1
     rw [qo] at h2
     simp only [hoff,↓reduceIte,nLA,nTA,nTB,
       show 6*i+off < 6*m by omega,decide_true,bATR] at h2
     change (c.goalv >>> sh).testBit (6*i+off)=_ at h2
     rw [nTS,← nAA] at h2
     rw [← hbit_goal (sh+6*i+off) (by omega)]
     exact h2
   exact ⟨by simpa using htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
          htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)⟩
 refine ⟨hsh0,h01,h1t,hp0d,hp1d,hall1,hgoal,hlok,hm0all,hm0,ha29_0,hb5_0,hm1,hm12,ha29_1,hb5_1,?_,?_,?_⟩
 . intro i hi
   constructor
   . have h1:=congrArg (fun z => z.testBit i) hcov0
     rw [nLA,nTA,hlok,nTB,nZT] at h1
     simp only [hi,decide_true,bATR] at h1
     rw [← hbit_goal i (by omega)];exact h1
   . have h1:=congrArg (fun z => z.testBit i) hcov1
     rw [nLA,nTA,hlok,nTB] at h1
     simp only [hi,decide_true,bATR] at h1
     change (c.goalv >>> c.k).testBit i=true at h1
     rw [nTS] at h1
     rw [← hbit_goal (c.k+i) (by omega)];exact h1
 . apply hlane7 c.sh0 ((c.sh1 - c.sh0) / 6) (by omega)
   rw [← hm0all];exact hp0m
 . apply hlane7 c.sh1 ((c.shTT - c.sh1) / 6) (by omega) hp1m
def AllTagsLe3 {α:Type} (ws:List (α × Nat)):Prop:=∀ p ∈ ws,p.2<=3
lemma AllTagsLe3.perm {α:Type} {xs ys:List (α × Nat)} (hp:xs.Perm ys)
   (h:AllTagsLe3 xs):AllTagsLe3 ys :=
 fun p hm => h p (hp.symm.subset hm)
lemma TagRun.inv_zero {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal 0 ws) :
   ∃ tg,ws=[(goal,tg)]:=by
 generalize hs:(0:Nat)=s at h
 induction h with
 | done tg => exact ⟨tg,rfl⟩
 | perm hp _ ih =>
   obtain ⟨tg,rfl⟩:=ih hs
   exact ⟨tg,List.perm_singleton.1 hp.symm⟩
 | uNot _ _ _ _ _ _ _ _ _ => cases hs
 | bOr _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
lemma TagRun.inv_succ {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s:Nat} {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal (s+1) ws) :
   (∃ a ta r save,ws.Perm ((a,ta)::r) /\
     ta≠1/\ta≠2/\(ta=3->save=false) /\
     inv a≠zero/\inv a≠one/\inv a≠a/\(∀ x ∈ r,x.1≠inv a) /\
     TagRun inv meet join zero one goal s ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r)) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠2/\tb≠2/\(ta=1->ka=false)/\(tb=1->kb=false) /\
     join a b≠zero/\join a b≠one/\join a b≠a/\join a b≠b/\(∀ x ∈ r,x.1≠join a b) /\
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r))) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠1/\tb≠1/\(ta≠0->ka=false)/\(tb≠0->kb=false) /\
     meet a b≠zero/\meet a b≠one/\meet a b≠a/\meet a b≠b/\(∀ x ∈ r,x.1≠meet a b) /\
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize hs:s+1=s' at h
 induction h with
 | done _ => cases hs
 | perm hp _ ih =>
   rcases ih hs with ⟨a,ta,r,save,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩
   . exact Or.inl ⟨a,ta,r,save,hp.symm.trans hp',rest⟩
   . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
   . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
 | @uNot s0 a ta r save h1 h2 h3 h4 h5 h6 h7 hsub _ =>
   cases hs
   exact Or.inl ⟨a,ta,r,save,lPR _,h1,h2,h3,h4,h5,h6,h7,hsub⟩
 | @bOr s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
 | @bAnd s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
lemma q68 {α:Type} {ws:List α} {a : α} {r:List α} (hp:ws.Perm (a::r)) :
   ∃ pre suf,ws=pre++a::suf/\r.Perm (pre++suf):=by
 have hmem:a ∈ ws:=hp.symm.subset (by simp)
 obtain ⟨pre,suf,hws⟩:=List.append_of_mem hmem
 refine ⟨pre,suf,hws,?_⟩
 rw [hws] at hp
 exact (List.perm_cons a).1 (hp.symm.trans lPM)
lemma q67 {α:Type} {ws:List α} {a b : α} {r:List α} (hp:ws.Perm (a::b::r)) :
   (∃ pre mid suf,ws=pre++a::mid++b::suf/\r.Perm (pre++mid++suf)) \/
   (∃ pre mid suf,ws=pre++b::mid++a::suf/\r.Perm (pre++mid++suf)):=by
 obtain ⟨p1,s1,hws,hbr⟩:=q68 hp
 have hmem:b ∈ p1++s1:=hbr.subset (by simp)
 rcases List.mem_append.1 hmem with hbp | hbs
 . obtain ⟨pre,mid,hp1⟩:=List.append_of_mem hbp
   right
   refine ⟨pre,mid,s1,by rw [hws,hp1,lAA,lCA],?_⟩
   rw [hp1,lAA] at hbr
   have hmid:(pre++b::(mid++s1)).Perm (b::(pre++(mid++s1))):=lPM
   have h1:=(List.perm_cons b).1 (hbr.trans hmid)
   simpa [lAA] using h1
 . obtain ⟨mid,suf,hs1⟩:=List.append_of_mem hbs
   left
   refine ⟨p1,mid,suf,by simp [hws,hs1,lAA],?_⟩
   rw [hs1] at hbr
   have hmid:((p1++mid)++b::suf).Perm (b::((p1++mid)++suf)):=lPM
   rw [← lAA] at hbr
   exact (List.perm_cons b).1 (hbr.trans hmid)
lemma z4 {α:Type} (k:Bool) (a : α) (r:List α) (x : α) :
   x ∈ qk k a r ↔ (k=true/\x=a)\/x ∈ r:=by
 cases k <;> simp [qk]
lemma yd {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (u v:Fin n->Bool) (hu:f u=false) (hv:f v=true) :
   ∃ p ∈ ws,p.1 u≠p.1 v:=by
 induction h with
 | done tg => exact ⟨(f,tg),by simp,by simp [hu,hv]⟩
 | perm hp _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   exact ⟨p,hp.subset hm,hne⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . exact ⟨(a,ta),by simp,fun e => hne (by dsimp only at e;simp [invF,e])⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . exact ⟨p,by simp [hm3],hne⟩
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [joinF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [meetF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
lemma zk {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (joinF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [joinF,Bool.or_eq_false_iff,bOT] at hu hv
   rcases hv with hva | hvb
   . exact ⟨(a,ta),by simp,hu.1,hva⟩
   . exact ⟨(b,tb),by simp,hu.2,hvb⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩
lemma za {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (meetF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [meetF,Bool.and_eq_false_iff,bAT] at hu hv
   rcases hu with hua | hub
   . exact ⟨(a,ta),by simp,hua,hv.1⟩
   . exact ⟨(b,tb),by simp,hub,hv.2⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩
lemma qf {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1) :
   ∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true:=by
 induction h with
 | done tg => intro u v hu hv;exact ⟨(f,tg),by simp,hu,hv⟩
 | perm hp _ ih =>
   intro u v hu hv
   obtain ⟨p,hm,h1,h2⟩:=ih (by rw [hp.length_eq];exact hlen) u v hu hv
   exact ⟨p,hp.subset hm,h1,h2⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact zk (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact za (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
lemma kk {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1)
   (r0 r1 r2 r3 r4 r5:Fin n->Bool)
   (h0:f r0=true) (h1:f r1=true) (h2:f r2=true)
   (h3:f r3=false) (h4:f r4=false) (h5:f r5=false) :
   3<=(ws.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
 induction h with
 | done tg => simp [h0,h1,h2,h3,h4,h5,q122]
 | perm hp _ ih =>
   rw [← (hp.map _).sum_eq]
   exact ih (by rw [hp.length_eq];exact hlen)
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at hih ⊢
   have hsub6:=w4 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at hih ⊢
   have hsub6:=kl (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
lemma qh {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s) :
   (∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) \/
   (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum):=by
 induction h with
 | done tg => simp at hlen
 | perm hp _ ih =>
   rcases ih (by rw [hp.length_eq];exact hlen) with hcov | hsym
   . left;intro u v hu hv
     obtain ⟨p,hm,h1,h2⟩:=hcov u v hu hv
     exact ⟨p,hp.subset hm,h1,h2⟩
   . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     rw [← (hp.map _).sum_eq]
     exact hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save
   . right
     intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hv:=kk hsub (by simp [qk] at hlen ⊢;omega) r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hle_s:∀ l:List (BFn n × Nat),
         (l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
         (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
       intro l;induction l with
       | nil => simp
       | cons x t iht =>
         simp only [lMC,List.sum_cons]
         have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5)
         omega
     have hs:=le_trans hv (hle_s _)
     simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs ⊢
     exact hs
   . simp [qk] at hlen hle;omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact zk (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at h1 ⊢
       have hsub6:=q14 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact zk (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact zk (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact za (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at h1 ⊢
       have hsub6:=je (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact za (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact za (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
abbrev aR (n rp:Nat) (c:Cfg):=allRows n rp c.shTT
abbrev TR {n:Nat} (f:BFn n):=TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f
lemma qz {a b:Nat} (h:a=b):Nat.beq a b=true:=Eq.mpr Nat.beq_eq h
lemma q0 (a:Nat):Nat.beq a a=true:=Eq.mpr Nat.beq_eq rfl
lemma q2 {a b:Nat} (h:a≠b):Nat.beq a b=false:=by
 cases hb:Nat.beq a b
 . rfl
 . exact absurd (Eq.mp Nat.beq_eq hb) h
lemma y3 {a b:Nat} (h:Nat.beq a b=false):a≠b :=
 fun e => by subst e;rw [q0] at h;cases h
lemma zh {a b:Nat}:(Nat.beq a b=false) ↔ a≠b :=
 ⟨y3,q2⟩
lemma q4 {b e:Bool} (h:e=true):(if b=true then true else e)=true:=by
 cases b <;> simp [h]
lemma q5 {b e:Bool} (h:b=true):(if b=true then true else e)=true:=by
 rw [h];rfl
lemma v8 (a b:Nat):Nat.add a b=a+b:=rfl
def encWs {n:Nat} (rows:List Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encL rows p.1,p.2)
abbrev eW {n:Nat} (rp:Nat) (c:Cfg) (ws:List (BFn n × Nat)):=encWs (aR n rp c) ws
abbrev eL {n:Nat} (rp:Nat) (c:Cfg) (g:BFn n):=encL (aR n rp c) g
lemma q41 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (joinF a b)=Nat.lor (eL rp c a) (eL rp c b):=q144 _ a b
lemma q40 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (meetF a b)=Nat.land (eL rp c a) (eL rp c b):=q143 _ a b
def encTTWs (n:Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encTT n p.1,p.2)
lemma qy {n:Nat} (rows:List Nat) (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encWs rows (p::ws)=(encL rows p.1,p.2)::encWs rows ws:=rfl
lemma kj {n:Nat} (rows:List Nat) (xs ys:List (BFn n × Nat)) :
   encWs rows (xs++ys)=encWs rows xs++encWs rows ys:=lMA
lemma q49 {n:Nat} (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encTTWs n (p::ws)=(encTT n p.1,p.2)::encTTWs n ws:=rfl
lemma q18 (xs ys:List (Nat × Nat)):qx xs ys=xs.reverse++ys:=by
 induction xs generalizing ys with
 | nil => rfl
 | cons a t ih => simp [qx,ih,lAA]
lemma q187 (ws:List (Nat × Nat)):q164 ws=ws.length:=by
 induction ws with
 | nil => rfl
 | cons _ t ih => simp [q164,ih,v8];omega
lemma wh (x:Nat) (ws:List (Nat × Nat)) :
   yz x ws=false ↔ ∀ p ∈ ws,p.1≠x:=by
 induction ws with
 | nil => simp [yz]
 | cons a t ih =>
   rcases a with ⟨w,tg⟩
   simp only [yz,lMM,forall_eq_or_imp]
   by_cases h:x=w
   . subst h;simp [q0]
   . simp [q2 h,ih,Ne.symm h]
lemma jo {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (ws:List (BFn n × Nat)) (g:BFn n)
   (h0:g≠fun _ => false) (h1:g≠fun _ => true) (hmem:∀ p ∈ ws,p.1≠g) :
   qj c.all1v (eW rp c ws) (eL rp c g)=true:=by
 have hinj:=q89 (n:=n) (q106 rp c.shTT)
 have hlen:(aR n rp c).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hne0:eL rp c g≠0:=fun e => by
   rw [← q39 (n:=n) (aR n rp c)] at e;exact h0 (hinj e)
 have hne1:eL rp c g≠c.all1v:=fun e => by
   rw [hc.all1v_eq,← hlen,← q177 (n:=n) (aR n rp c)] at e;exact h1 (hinj e)
 have hnc:yz (eL rp c g) (eW rp c ws)=false:=by
   rw [wh]
   intro p hp;rcases List.mem_map.1 hp with ⟨q,hq,rfl⟩
   exact fun e => hmem q hq (hinj e)
 unfold qj
 simp [q2 hne0,q2 hne1,hnc]
lemma qc {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (joinF a b)=Nat.lor (encL rows a) (encL rows b):=q144 rows a b
lemma q9 {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (meetF a b)=Nat.land (encL rows a) (encL rows b):=q143 rows a b
lemma q145 {n:Nat} (rows:List Nat) (a:BFn n) :
   encL rows (invF a)=Nat.xor (encL rows a) (2 ^ rows.length - 1):=q160 rows a
lemma qv {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:BFn n) :
   eL rp c (invF a)=Nat.xor (eL rp c a) c.all1v:=by
 unfold eL;rw [q160,zl,← hc.all1v_eq]
def wi (c:Cfg) (w:Nat):Nat:=Nat.land w c.lok
def q63 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.k) c.lok
def k1 (c:Cfg) (w:Nat):Nat:=Nat.xor c.lok (q63 c w)
def wC (c:Cfg) (w:Nat):Nat:=Nat.xor (wi c w) (q63 c w)
def wU (c:Cfg) (w:Nat):Nat:=Nat.land (wC c w) (q63 c w)
def wA0 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
def wV0 (c:Cfg) (w:Nat):Nat:=qi c.m0 (wA0 c w)
def wV1 (c:Cfg) (w:Nat):Nat:=yg c.sh1 c.m1 c.m12 w
def yx (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wC c p.1) acc) 0
def v4 (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wU c p.1) acc) 0
def zf (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0
def va (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0
lemma qq (a b d:Nat):Nat.lor (Nat.lor a b) d=Nat.lor a (Nat.lor b d):=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_assoc]
lemma q7 (a b:Nat):Nat.lor a b=Nat.lor b a:=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_comm]
lemma q108 (a b:Nat):Nat.land a b=Nat.land b a:=by
 apply nEQ;intro i;simp [nLA,nTA,Bool.and_comm]
lemma q46 (a:Nat):Nat.lor 0 a=a:=by
 apply nEQ;intro i;simp [nLO,nTO]
lemma qt (a b:Nat):Nat.add a b=Nat.add b a:=nAC a b
lemma y9 (a b d:Nat):Nat.add (Nat.add a b) d=Nat.add a (Nat.add b d):=nAA a b d
lemma yp (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):yx c (p::ws)=Nat.lor (wC c p.1) (yx c ws):=rfl
lemma vo (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):v4 c (p::ws)=Nat.lor (wU c p.1) (v4 c ws):=rfl
lemma k0 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):zf c (p::ws)=Nat.add (wV0 c p.1) (zf c ws):=rfl
lemma w1 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):va c (p::ws)=Nat.add (wV1 c p.1) (va c ws):=rfl
lemma vc (c:Cfg) (xs ys:List (Nat × Nat)):yx c (xs++ys)=Nat.lor (yx c xs) (yx c ys):=by
 induction xs with | nil => simp [yx,q46] | cons a t ih => simp only [lCA,yx,lFC] at ih ⊢;rw [ih,qq]
lemma zu (c:Cfg) (xs ys:List (Nat × Nat)):v4 c (xs++ys)=Nat.lor (v4 c xs) (v4 c ys):=by
 induction xs with | nil => simp [v4,q46] | cons a t ih => simp only [lCA,v4,lFC] at ih ⊢;rw [ih,qq]
lemma zy (c:Cfg) (xs ys:List (Nat × Nat)):zf c (xs++ys)=Nat.add (zf c xs) (zf c ys):=by
 induction xs with | nil => simp [zf,v8] | cons a t ih => simp only [lCA,zf,lFC,v8] at ih ⊢;omega
lemma y6 (c:Cfg) (xs ys:List (Nat × Nat)):va c (xs++ys)=Nat.add (va c xs) (va c ys):=by
 induction xs with | nil => simp [va,v8] | cons a t ih => simp only [lCA,va,lFC,v8] at ih ⊢;omega
lemma yo (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):yx c xs=yx c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [yx,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [yx,lFC];rw [← qq,q7 (wC c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma y0 (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):v4 c xs=v4 c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [v4,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [v4,lFC];rw [← qq,q7 (wU c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma vu (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):zf c xs=zf c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [zf,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [zf,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma kz (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):va c xs=va c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [va,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [va,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma q149 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (yx c ws).testBit i=ws.any (fun p => (wC c p.1).testBit i):=by
 induction ws with
 | nil => simp [yx]
 | cons _ _ ih => simp only [yx,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma q148 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (v4 c ws).testBit i=ws.any (fun p => (wU c p.1).testBit i):=by
 induction ws with
 | nil => simp [v4]
 | cons _ _ ih => simp only [v4,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma zw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wi c w).testBit i=if i < c.k then w.testBit i else false:=by
 unfold wi;rw [nLA,nTA,hc.lok_eq,nTB]
 by_cases hi:i < c.k <;> simp [hi]
lemma vl {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (q63 c w).testBit i=if i < c.k then w.testBit (c.k+i) else false:=by
 unfold q63;rw [nLA,nTA,hc.lok_eq,nTB]
 change ((w >>> c.k).testBit i&&decide (i < c.k))=_
 rw [nTS];by_cases hi:i < c.k <;> simp [hi]
lemma q13 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (k1 c w).testBit i=if i < c.k then !(w.testBit (c.k+i)) else false:=by
 unfold k1;rw [nXO,nTX,hc.lok_eq,nTB,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma vp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wC c w).testBit i=if i < c.k then (w.testBit i ^^ w.testBit (c.k+i)) else false:=by
 unfold wC;rw [nXO,nTX,zw hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma vd {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wU c w).testBit i=if i < c.k then (!(w.testBit i)&&w.testBit (c.k+i)) else false:=by
 unfold wU;rw [nLA,nTA,vp hc,vl hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases w.testBit i <;> cases w.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q197 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wC c (Nat.xor a c.all1v)=wC c a:=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vp hc,vp hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q168 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wU c (Nat.xor a c.all1v)=Nat.land (wC c a) (wi c a):=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vd hc,nLA,nTA,vp hc,zw hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q78 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   Nat.lor (wU c (Nat.xor a c.all1v)) (wU c a)=wC c a:=by
 rw [q168 hc];apply nEQ;intro i
 rw [nLO,nLA,nTO,nTA,vp hc,zw hc,vd hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q169 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.lor a b)=Nat.xor (Nat.lor (wi c a) (wi c b)) (Nat.lor (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLO,nLO,nLO,
     nTX,nTO,nTO,nTO,nTO,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma q121 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.land a b)=Nat.xor (Nat.land (wi c a) (wi c b)) (Nat.land (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLA,nLA,nLA,
     nTX,nTA,nTA,nTA,nTA,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma q170 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wA0 c (Nat.xor a c.all1v)=Nat.xor (wA0 c a) c.m0all:=by
 have h2n:=n2P n
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nXO,nTA,nTX,hc.m0all_eq,nTB]
 change (((a^^^c.all1v) >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) =
   (((a >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) ^^ decide (i < 6*((c.sh1 - c.sh0) / 6)))
 rw [nTS,nTS,nTX,hc.all1v_eq,nTB]
 by_cases hi:i < 6*((c.sh1 - c.sh0) / 6)
 . simp [hi,show c.sh0+i < c.shTT+2 ^ n by omega]
 . simp [hi]
lemma q198 (c:Cfg) (a b:Nat):wA0 c (Nat.lor a b)=Nat.lor (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nLO,nTA,nTO]
 change (((a|||b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)||((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTO]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide
lemma q171 (c:Cfg) (a b:Nat):wA0 c (Nat.land a b)=Nat.land (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nTA]
 change (((a&&&b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)&&((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTA]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide
lemma q200 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wV1 c (Nat.xor a c.all1v)=wV1 c a:=by
 have h2n:=n2P n
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 apply wg;intro i;unfold wV1
 rw [hc.m1_eq,hc.m12_eq,kh,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show c.sh1+6*i < c.shTT+2 ^ n by omega,show c.sh1+6*i+1 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+2 < c.shTT+2 ^ n by omega,show c.sh1+6*i+3 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+4 < c.shTT+2 ^ n by omega,show c.sh1+6*i+5 < c.shTT+2 ^ n by omega,
     decide_true,bBT,jp]
 . simp [hi]
lemma y4 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.lor a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0/\Nat.land (Nat.xor c.lok rU) (wi c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,zw hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])
lemma q10 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.lor a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,zw hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]
lemma vw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.land a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0/\Nat.land (Nat.xor c.lok rU) (k1 c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,q13 hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])
lemma jb {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.land a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,q13 hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]
lemma wk {m x y:Nat} (hx:Nat.land m x=0) (hy:Nat.land m y=0) :
   Nat.land m (Nat.lor x y)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hx
 have h2:=congrArg (fun z => z.testBit i) hy
 simp only [nLA,nLO,nTA,nTO,nZT] at h1 h2 ⊢
 revert h1 h2;cases m.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> decide
lemma zz {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u≠p.1 v) :
   yx c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q149,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hne⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vp hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega)]
   cases h1:p.1 (q1 n ((aR n rp c).getD i 0)) <;>
     cases h2:p.1 (q1 n ((aR n rp c).getD (c.k+i) 0)) <;> simp_all
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vp hc,if_neg hi] at htb;cases htb
lemma q6 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) :
   v4 c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q148,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hpu,hpv⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vd hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),hpu,hpv];rfl
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vd hc,if_neg hi] at htb;cases htb
lemma q112 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV0 c (eL rp c g)) i =
     if i < (c.sh1 - c.sh0) / 6 then
       let rows:=aR n rp c
       v6 (g (q1 n (rows.getD (c.sh0+6*i) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 unfold wV0;rw [hc.m0_eq,yy]
 by_cases hi:i < (c.sh1 - c.sh0) / 6
 . simp only [hi,↓reduceIte]
   have htb:∀ off < 6,(wA0 c (eL rp c g)).testBit (6*i+off) =
       g (q1 n ((aR n rp c).getD (c.sh0+6*i+off) 0)):=by
     intro off hoff;unfold wA0
     rw [nLA,nTA,hc.m0all_eq,nTB]
     simp only [show 6*i+off < 6*((c.sh1 - c.sh0) / 6) by omega,decide_true,bATR]
     change ((eL rp c g) >>> c.sh0).testBit (6*i+off)=_
     rw [nTS,← nAA,qm _ _ (by rw [hlen];omega)]
   rw [show 6*i=6*i+0 by omega,htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
       htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)]
   simp only [nAZ]
 . simp [hi]
lemma q111 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV1 c (eL rp c g)) i =
     if i < (c.shTT - c.sh1) / 6 then
       let rows:=aR n rp c
       zq (g (q1 n (rows.getD (c.sh1+6*i) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte]
   rw [qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega)]
 . simp [hi]
lemma zi {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {g:BFn n} {tg:Nat} {r:List (BFn n × Nat)}
   (hs:s<=10)
   (htr:TR f s ((g,tg)::r))
   (hlen:((g,tg)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (wV0 c (eL rp c g))=true:=by
 set rows:=aR n rp c
 set m:=(c.sh1 - c.sh0) / 6
 have hsum:Nat.add (zf c (encWs rows r)) (wV0 c (encL rows g))=zf c (encWs rows ((g,tg)::r)):=by
   simp only [encWs,lMC,zf,lFC,v8];omega
 unfold qb;rw [hsum,hc.a29_0_eq,hc.b5_0_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV0 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV0;rw [hc.m0_eq,yy];split;exact yr _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV0 c p.1) m hf_le (encWs rows ((g,tg)::r)) (by rw [encWs,lLM,hlen];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ((g,tg)::r)).length=s+1:=by rw [encWs,lLM,hlen]
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ((g,tg)::r)).map fun p => z6 (wV0 c p.1) i) =
       ((g,tg)::r).map fun p =>
         v6 (p.1 (q1 n (rows.getD (c.sh0+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q112 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p0_ok i hi
   exact kk htr hlen _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'
lemma vt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)} (hlen:ws.length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (va c (eW rp c ws))=true:=by
 set rows:=aR n rp c
 set m:=(c.shTT - c.sh1) / 6
 unfold z3;rw [hc.a29_1_eq,hc.b5_1_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV1 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh];split;exact q52 _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV1 c p.1) m hf_le (encWs rows ws) (by rw [encWs,lLM];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ws).length=ws.length:=lLM _
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ws).map fun p => z6 (wV1 c p.1) i) =
       ws.map fun p =>
         zq (p.1 (q1 n (rows.getD (c.sh1+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q111 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p1_ok i hi
   exact hsym _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'
abbrev PN (c:Cfg) (w tg:Nat) (l2:List (Nat × Nat)) (pl2:PList):PList :=
 PList.cons w tg (wi c w) (q63 c w) (k1 c w) (wC c w) (wU c w) (wA0 c w) (wV0 c w) (wV1 c w)
   (yx c l2) (v4 c l2) (zf c l2) (va c l2) pl2
inductive PListSpec (c:Cfg):PList->List (Nat × Nat)->Prop where
 | nil:PListSpec c PList.nil []
 | cons (w tg:Nat) (tl:PList) (rest:List (Nat × Nat)) :
     PListSpec c tl rest ->
     PListSpec c
       (PN c w tg rest tl)
       ((w,tg)::rest)
lemma q82 (c:Cfg) (ws:List (Nat × Nat)) :
   ∃ pl,kt c ws=(yx c ws,v4 c ws,zf c ws,va c ws,pl)/\PListSpec c pl ws:=by
 induction ws with
 | nil => exact ⟨PList.nil,rfl,PListSpec.nil⟩
 | cons p rest ih =>
   rcases p with ⟨w,tg⟩;obtain ⟨tl,htl,hsp⟩:=ih
   refine ⟨_,?_,PListSpec.cons w tg tl rest hsp⟩;simp only [kt,htl];rfl
lemma PListSpec.pToList {c:Cfg} {pl:PList} {ws:List (Nat × Nat)} (h:PListSpec c pl ws) :
   pToList pl=ws:=by
 induction h with | nil => rfl | cons _ _ _ _ _ ih => exact congrArg _ ih
lemma q84 (c:Cfg) (ws:List (Nat × Nat)) (a ta alo nahi a0 v0a:Nat)
   (pre mid:List (Nat × Nat)) (pmU pmV0:Nat) (pl:PList) :
   we c ws a ta alo nahi a0 v0a pmU pmV0 pl =
     vx c ws (fun _ => true) a ta alo nahi a0 v0a pre pmU pmV0 mid pl:=by
 induction pl generalizing pmU pmV0 mid with
 | nil => rfl
 | cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post ih =>
   simp only [we,vx]
   have hor :
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          okOrB&&qj c.all1v ws w||!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)
        else false) =
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          if (okOrB&&qj c.all1v ws w&&true)=true then true
          else if (!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land blo).beq 0 <;> cases qj c.all1v ws (a.lor b) <;>
         cases ta.beq 1 <;> cases tb.beq 1 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.lor b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0)) <;> rfl
       . split <;> simp
   have hand :
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          okAndB&&qj c.all1v ws w||ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)
        else false) =
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          if (okAndB&&qj c.all1v ws w&&true)=true then true
          else if (ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land nbhi).beq 0 <;> cases qj c.all1v ws (a.land b) <;>
         cases ta.beq 0 <;> cases tb.beq 0 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.land b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0)) <;> rfl
       . split <;> simp
   rw [hor,hand,ih ((b,tb)::mid) (Nat.lor pmU ub) (Nat.add pmV0 v0b)]
lemma q140 (c:Cfg) (ws:List (Nat × Nat)) (preU preV0:Nat) (pre:List (Nat × Nat)) (pl:PList) :
   q26 c ws preU preV0 pl=js c ws (fun _ => true) preU preV0 pre pl:=by
 induction pl generalizing preU preV0 pre with
 | nil => rfl
 | cons a ta alo ahi nahi ca ua a0 v0a v1a postC postU postV0 postV1 suf ih =>
   simp only [q26,js,q84 c ws a ta alo nahi a0 v0a pre [] preU preV0 suf]
   split;rfl;exact ih _ _ _
lemma wu (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) :
   scanInline c s ws=scanAll c s ws (fun _ => true):=by
 unfold scanInline scanAll
 split
 . rfl
 . cases kt c ws with
   | mk totC r1 => cases r1 with
   | mk totU r2 => cases r2 with
   | mk totV0 r3 => cases r3 with
   | mk totV1 pl =>
     dsimp only
     cases Nat.sub (Nat.add s 2) (q164 ws) with
     | zero => rfl
     | succ d =>
       cases d with
       | zero =>
         cases z3 c totV1
         . simp only [bFT,↓reduceIte];rw [q140 c ws 0 0 []]
         . rfl
       | succ d2 => cases d2 <;> rfl
lemma y8 {α:Type} (x : α) (a b:List α):(x::a++b).Perm (a++x::b) :=
 List.perm_middle.symm
lemma v7 {α:Type} (p:List α) (x : α) (a b:List α) :
   (p++x::a++b).Perm (p++a++x::b):=by
 simpa [lAA] using (lPM (a:=x) (l₁:=a) (l₂:=b)).symm.append_left p
lemma q130 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w7 c ws onSurv (v4 c (pre++l1)) (zf c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w7 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w7;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q128 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w6 c ws onSurv (yx c (pre++l1)) (v4 c (pre++l1)) (zf c (pre++l1)) (va c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w6 c ws onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w6;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q126 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w5 c ws onSurv (yx c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w5 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w5;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q132 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold ke;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q97 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q98 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q98;apply q5
     apply q132 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q98;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q105 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold vx;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q65 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   js c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold js;apply q5
     apply q105 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold js;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q131 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV0 pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid))
   (hV0:pmV0=zf c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmC pmU pmV0 pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV0 pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kd;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q95 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q96 c ws hasUp onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q96;apply q5
     apply q131 c ws hasUp onSurv a ta pre mid l2 [] b tb preC preU preV0 preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV0]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q96;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q129 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre pmC pmU pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kc;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q93 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q94 c ws hasUp totV0 onSurv preC preU preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q94;apply q5
     apply q129 c ws hasUp totV0 onSurv a ta pre mid l2 [] b tb preC preU preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q94;apply q4
     apply ih ((w,tg)::pre) _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q127 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2)) (hC:pmC=yx c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre
       (yx c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre pmC mid pl=true:=by
 induction m1 generalizing mid pmC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold k9;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q91 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q92 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q92;apply q5
     apply q127 c ws onSurv a ta pre mid l2 [] b tb preC tl htl (by simp [hC])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q92;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q81 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (htr:TR f 1 ws) :
   j6 c (eW rp c ws)=true:=by
 set rows:=aR n rp c
 have hlen_rows:=zl n rp c.shTT
 rcases htr.inv_succ with
   ⟨a,ta,r,save,hperm,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases save <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hinv,_⟩,rfl⟩:=heq
     rw [List.perm_singleton.1 hperm];simp only [encWs,lMC,List.map_nil,j6,Nat.beq_eq]
     rw [← qv hc,hinv,hc.goalv_eq]
   . cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hj,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . left;rw [← qc,hj,hc.goalv_eq]
     . left;rw [q7,← qc,hj,hc.goalv_eq]
   all_goals cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hm,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . right;rw [← q9,hm,hc.goalv_eq]
     . right;rw [q108,← q9,hm,hc.goalv_eq]
   all_goals cases heq.2
lemma jc {α:Type} {a w : α} {ta:Nat} {r:List (α × Nat)} {save:Bool}
   (h:AllTagsLe3 ((a,ta)::r)):AllTagsLe3 ((w,if ta=3 then 2 else 0)::qk save (a,0) r):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . exact h p (List.mem_cons_of_mem _ hp3)
lemma k5 {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;split <;> omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;split <;> omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))
lemma yw {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))
lemma kv {n:Nat} (a b:BFn n):joinF a b=joinF b a:=by funext x;simp [joinF,Bool.or_comm]
lemma ku {n:Nat} (a b:BFn n):meetF a b=meetF b a:=by funext x;simp [meetF,Bool.and_comm]
lemma q137 {α:Type} (ka kb:Bool) (a b : α) (r:List α) :
   (qk ka a (qk kb b r)).Perm (qk kb b (qk ka a r)):=by
 cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte]
 . exact lPR _
 . exact lPR _
 . exact lPR _
 . exact List.Perm.swap _ _ _
lemma ql {α:Type} (l1 mid l2:List α) (a b : α) :
   (l1++a::mid++b::l2).Perm (a::b::(l1++mid++l2)):=by
 have h1:(l1++a::(mid++b::l2)).Perm (a::(l1++mid++b::l2)):=by
   simpa [lAA] using (lPM (a:=a) (l₁:=l1) (l₂:=mid++b::l2))
 have h2:(l1++mid++b::l2).Perm (b::(l1++mid++l2)) :=
   lPM (a:=b) (l₁:=l1++mid) (l₂:=l2)
 simpa [lAA] using h1.trans (lPC a h2)
lemma q135 (a b d:Nat):Nat.lor (Nat.lor d b) a=Nat.lor a (Nat.lor b d):=by
 rw [q7 _ a,q7 d b]
lemma jq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((joinF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.lor (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.lor (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,qc,q169 hc] at h0
 rw [q7];exact h0
lemma wq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((meetF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.land (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.land (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,q9,q121 hc] at h0
 rw [q7];exact h0
lemma zx {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((w,tw)::(x,tx)::r)) :
   Nat.lor (Nat.lor (yx c (eW rp c r)) (wC c (eL rp c x)))
     (wC c (eL rp c w))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp] at h0
 rw [q135];exact h0
lemma zp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (wi c (eL rp c a))=0:=by
 apply q10 hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0
lemma zn {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (k1 c (eL rp c a))=0:=by
 apply jb hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0
lemma yj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)} (hlen:((w,tw)::(x,tx)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,tw)::(x,tx)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h1:=vt hc hlen hsym
 simp only [qy,w1] at h1
 have heq:Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (wV1 c (eL rp c w)) =
     Nat.add (wV1 c (eL rp c w))
       (Nat.add (wV1 c (eL rp c x)) (va c (eW rp c r))):=by
   simp only [v8];omega
 rw [show yg c.sh1 c.m1 c.m12 (eL rp c w)=wV1 c (eL rp c w) from rfl,heq]
 exact h1
lemma k2 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.lor (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0;rw [q7];exact h0
lemma yt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.land (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0;rw [q7];exact h0
lemma kr {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::r))
   (hlen:((joinF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q41,q198] at h0;exact h0
lemma k8 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::r))
   (hlen:((meetF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q40,q171] at h0;exact h0
lemma vq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::(x,tx)::r))
   (hlen:((joinF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q41,q198] at h0;exact h0
lemma vf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::(x,tx)::r))
   (hlen:((meetF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q40,q171] at h0;exact h0
lemma q16 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::r))
   (hlen:((invF a,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0
lemma q15 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::(a,tx)::r))
   (hlen:((invF a,t)::(a,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c a)))
     (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0
lemma jf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w:BFn n} {t:Nat} {r:List (BFn n × Nat)} (hlen:((w,t)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,t)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (va c (eW rp c r)) (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h0:=vt hc hlen hsym
 simp only [qy,w1] at h0;rw [qt] at h0;exact h0
lemma q17 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b)
   (onSurv:List (Nat × Nat)->Bool)
   (hon:∀ zs_b,AllTagsLe3 zs_b ->
     TR f s zs_b ->
     onSurv (eW rp c zs_b)=true) :
   scanAll c s (eW rp c ws_b) onSurv=true:=by
 cases s with
 | zero => unfold scanAll;simp only [q0,↓reduceIte];exact q81 hc htr
 | succ s' =>
   have hs_nz:Nat.beq (s'+1) 0=false:=q2 (Nat.succ_ne_zero s')
   unfold scanAll;simp only [hs_nz,bFT,↓reduceIte]
   obtain ⟨pl,hprep,hsp⟩:=q82 c (eW rp c ws_b)
   rw [hprep];dsimp only;rw [q187,show (eW rp c ws_b).length=ws_b.length from lLM _]
   have hws_len_le:ws_b.length<=s'+3:=htr.len_le
   have hun_split:∀ {a ta r save},ws_b.Perm ((a,ta)::r) ->
       ta≠1->ta≠2->(ta=3->save=false) ->
       invF a≠(fun _ => false)->invF a≠(fun _ => true)->invF a≠a->(∀ x ∈ r,x.1≠invF a) ->
       TR f (s'+1) ((invF a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
       ∃ l1 l2,ws_b=l1++(a,ta)::l2/\(save=true->ta=0) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (invF a))=true /\
         AllTagsLe3 ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) /\
         TR f (s'+1)
           ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)):=by
     intro a ta r save hp h1 h2 h3 h0 h1' hna hnr hsub
     have hvw:=jo hc ws_b (invF a) h0 h1' fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm;exact hnr p hpm2
     have htags':=htags.perm hp
     have hta_le:ta<=3:=htags' (a,ta) (by simp)
     have hsave0:save=true->ta=0:=fun hst => by
       have hne3:ta≠3:=fun e => by rw [h3 e] at hst;cases hst
       omega
     obtain ⟨l1,l2,hws,hrp⟩:=q68 hp
     have hkp:((invF a,if ta=3 then 2 else 0)::qk save (a,0) r).Perm
         ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) :=
       lPC _ (by cases save <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _)
     exact ⟨l1,l2,hws,hsave0,hvw,(jc htags').perm hkp,TagRun.perm hkp hsub⟩
   have hor_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
       joinF a b≠(fun _ => false)->joinF a b≠(fun _ => true)->joinF a b≠a->joinF a b≠b->(∀ x ∈ r,x.1≠joinF a b) ->
       TR f (s'+1)
         ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠2/\tb'≠2/\(ta'=1->ka'=false)/\(tb'=1->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (joinF a' b'))=true /\
         AllTagsLe3 ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (joinF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF b a,0)::qk kb (b,if tb=3 then 1 else 0) (qk ka (a,if ta=3 then 1 else 0) (l1++mid++l2))):=by
         rw [kv b a];apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [kv a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
   have hand_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
       meetF a b≠(fun _ => false)->meetF a b≠(fun _ => true)->meetF a b≠a->meetF a b≠b->(∀ x ∈ r,x.1≠meetF a b) ->
       TR f (s'+1)
         ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠1/\tb'≠1/\(ta'≠0->ka'=false)/\(tb'≠0->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (meetF a' b'))=true /\
         AllTagsLe3 ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (meetF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF b a,if tb=3\/ta=3 then 1 else 0)::qk kb (b,0) (qk ka (a,0) (l1++mid++l2))):=by
         have hcond:(if tb=3\/ta=3 then 1 else 0)=(if ta=3\/tb=3 then 1 else 0):=by
           by_cases h1:ta=3 <;> by_cases h2:tb=3 <;> simp [h1,h2]
         rw [ku b a,hcond]
         apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [ku a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
   have hacc_rest:∀ (l1 mid l2:List (BFn n × Nat)),
       Nat.lor (yx c ([]++eW rp c l1++eW rp c mid)) (yx c (eW rp c l2))=yx c (eW rp c (l1++mid++l2)) /\
       Nat.lor (v4 c ([]++eW rp c l1++eW rp c mid)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++mid++l2)) /\
       Nat.add (zf c ([]++eW rp c l1++eW rp c mid)) (zf c (eW rp c l2))=zf c (eW rp c (l1++mid++l2)) /\
       Nat.add (va c ([]++eW rp c l1++eW rp c mid)) (va c (eW rp c l2))=va c (eW rp c (l1++mid++l2)) /\
       qx ((eW rp c l1).reverse++[]) (qx (eW rp c mid).reverse (eW rp c l2))=eW rp c (l1++mid++l2):=by
     intro l1 mid l2
     refine ⟨?_,?_,?_,?_,?_⟩
     . rw [← vc];simp [encWs,lAA]
     . rw [← zu];simp [encWs,lAA]
     . rw [← zy];simp [encWs,lAA]
     . rw [← y6];simp [encWs,lAA]
     . simp [q18,encWs,lAA]
   generalize hsl:Nat.sub (Nat.add (s'+1) 2) ws_b.length=slack
   cases slack with
   | zero =>
     have hlen:ws_b.length=s'+3:=by simp at hsl;omega
     have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc (qf htr hlen)
     simp only [hup,q0,bTA]
     rcases htr.inv_succ with
       ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
     . have hle:=hsub.len_le;have hp_len:=hp.length_eq
       cases save <;> simp [qk] at hlen hle hp_len <;> omega
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q5
       have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=k2 hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
       have hval0:=kr hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← qc,hvw,bTA]
       exact hsurv
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q4;apply q5
       have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=yt hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
       have hval0:=k8 hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← q9,hvw,hwt,bTA]
       exact hsurv
   | succ slack' =>
     cases slack' with
     | zero =>
       have hlen:ws_b.length=s'+2:=by simp at hsl;omega
       have hlen11:ws_b.length<=11:=by omega
       cases hsym1:z3 c (va c (eW rp c ws_b))
       . have hno_sym : ¬ (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
             3<=(ws_b.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :=
           fun h => by rw [vt hc hlen11 h] at hsym1;cases hsym1
         have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc ((qh htr hlen).resolve_right hno_sym)
         simp only [bFT,↓reduceIte,hup,q0,bTA]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . exfalso;have hle:=hsub.len_le;have hp_len:=hp.length_eq
           cases save
           . apply hno_sym;intro r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hv:=kk hsub (by simp [qk] at hlen hp_len ⊢;omega) r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hle_s:∀ l:List (BFn n × Nat),(l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
                 (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
               intro l;induction l with | nil => simp | cons x t iht => simp only [lMC,List.sum_cons];have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5);omega
             have hs1:=le_trans hv (hle_s _)
             simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs1
             rw [(hp.map _).sum_eq];exact hs1
           . simp [qk] at hlen hle hp_len;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,joinF] at h1s ⊢
               have:=q14 (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=k2 hc hch_up_p
             have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← qc,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [kv] at h0;exact zp hc h0
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))) 0=true:=qz hm2
             split
             . apply q4;apply q4
               simp only [q2 htb1,bNF,hokB,hval0,← qc,hvw,bTA,htb3];exact hsurv
             . simp only [hokB,q2 htb1,bNF,bTA,↓reduceIte,hval0,← qc,hvw,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zp hc (qf hsub' hch_len)
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             simp only [q2 hta1,bNF,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,meetF] at h1s ⊢
               have:=je (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=yt hc hch_up_p
             have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← q9,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [ku] at h0;exact zn hc h0
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))) 0=true:=qz hm2
             have hwt0:(if ta'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by subst htb0;simp [Nat.beq_eq]
             split
             . apply q4;apply q4
               rw [hwt];simp only [qz htb0,hokB,hval0,← q9,hvw,bTA];exact hsurv
             . rw [hwt0];simp only [hokB,qz htb0,bTA,↓reduceIte,hval0,← q9,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zn hc (qf hsub' hch_len)
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             rw [hwt];simp only [qz hta0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
       ·
         simp only [↓reduceIte,bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,_,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+l2.length+1=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           cases save
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc,q168 hc] at h0u
               rw [q7];exact h0u
             have hval0:=q16 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
             apply q130 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 pl hsp' rfl rfl
             intro pl2 hpl2;unfold w7;dsimp only;rw [hpl2.pToList,q18];apply q5
             have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
             have h1v:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [h1u,h1v,lANil,lRR,← kj,q2 hta1,q2 hta2,
               bNF,hch_up,q0,hval0,← qv hc,hvw,hta3b,bTA]
             exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=jq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=k2 hc hcu
               have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← qc,hvw];exact hsurv
             . have hcs':=jf hc (by omega:((joinF a' b',0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← qc,hcs',bOTR,bTA,hvw];exact hsurv
               . simp only [hcov,q0,← qc,hcs',bTA,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               rw [kv] at hcu;exact zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             simp only [q2 htb1,bNF,hm2,q0,hval0,← qc,hvw,bTA,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             simp only [q2 hta1,bNF,hm1,q0,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=wq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=yt hc hcu
               have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← q9,hvw,hwt];exact hsurv
             . have hcs':=jf hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← q9,hcs',bOTR,bTA,hvw,hwt];exact hsurv
               . simp only [hcov,q0,← q9,hcs',bTA,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               rw [ku] at hcu;exact zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             rw [hwt];simp only [qz htb0,hm2,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             rw [hwt];simp only [qz hta0,hm1,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
     | succ slack'' =>
       cases slack'' with
       | zero =>
         have hlen:ws_b.length=s'+1:=by simp at hsl;omega
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hl_eq:l1.length+l2.length+1=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q128 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold w6;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
           have h1v0:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
           have h1v1:Nat.add (va c ([]++eW rp c l1)) (va c (eW rp c l2))=va c (eW rp c (l1++l2)):=by rw [← y6];simp [encWs]
           simp only [h1c,h1u,h1v0,h1v1,lANil,lRR,q2 hta1,q2 hta2,
             bOS,bFT,↓reduceIte,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+1:=by simp;omega
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hor_u:(Nat.beq (Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))) c.lok ||
                 z3 c (Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a))))=true:=by
               rcases qh hsub' hch_len with hcu | hcs
               . have h0u:=q6 hc hcu
                 simp only [qy,vo,qv hc,q168 hc] at h0u
                 rw [q7] at h0u;rw [h0u,q0];rfl
               . have h1s:=vt hc (by omega:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length<=11) hcs
                 simp only [qy,w1,qv hc,q200 hc] at h1s
                 have hcomm:Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a)) =
                     Nat.add (wV1 c (eL rp c a)) (va c (eW rp c (l1++l2))):=by simp;omega
                 rw [hcomm,h1s];simp
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,hor_u,← qv hc,hvw,hta3b,← kj,bTA];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl
             rw [h03] at htc hsub'
             have hch_len:((invF a,0)::(a,0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc] at h0u
               rw [← qq,q78 hc,q7] at h0u;exact h0u
             have hval0:=q15 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hta0,q0,hch_up,hval0,← qv hc,hvw,← kj,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=jq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← qc,hvw,bTA,bOT]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
                 rw [kv] at hcu;exact zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               simp only [q2 htb1,bNF,hcov,hm2,q0,bTOR,← qc,hvw,htb3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,htb3b,bTA];exact hsurv
               . right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,hvw,htb3b,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               simp only [q2 hta1,bNF,hcov,hm1,q0,bTOR,← qc,hvw,hta3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,hta3b,bTA];exact hsurv
               . left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,hvw,hta3b,bTA];exact hsurv
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have htot_eq:zf c (eW rp c ((a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)))=zf c (eW rp c ws_b):=by
               have h1:zf c (eW rp c ws_b)=zf c (eW rp c ((a',ta')::(b',tb')::(l1++mid++l2))):=by
                 rw [hws];exact vu c ((ql l1 mid l2 _ _).map _)
               rw [h1];rfl
             have hval0:=kr hc hs hsub' hch_len;rw [htot_eq] at hval0
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [q2 hta1,q2 htb1,bNF,hval0,← qc,hvw,hta3b,htb3b,bTA]
             exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=wq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← q9,hvw,bTA,bOT,hwt_or]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
                 rw [ku] at hcu;exact zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               rw [hwt_or];simp only [qz htb0,hcov,hm2,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               rw [hwt_or];simp only [qz hta0,hcov,hm1,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_len:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             have hval0:=k8 hc hs (TagRun.perm hch_perm hsub') (by rw [← hch_perm.length_eq];exact hch_len)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [hta0,htb0,q0,hval0,← q9,hvw,bTA];exact hsurv
       | succ _ =>
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q126 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 pl hsp' rfl
           intro pl2 hpl2;unfold w5;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           simp only [h1c,lANil,lRR,q2 hta1,q2 hta2,
             bNF,bTA,← qv hc,hvw,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,bTA,hta3b,← kj];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl;rw [h03] at htc hsub'
             have hch_perm:((invF a,0)::(a,0)::(l1++l2)).Perm ((invF a,0)::ws_b) :=
               lPC _ (by rw [hws,hta0];exact List.perm_middle.symm)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hta0,q0,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← qc,hvw,bOT]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [jq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;right;simp only [q2 htb1,bNF,hcov,q0,htb3b,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;left;right;simp only [q2 hta1,bNF,hcov,q0,hta3b,bTA];exact hon _ htc hsub'
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             right;simp only [q2 hta1,q2 htb1,bNF,hta3b,htb3b,bTA];exact hon _ htc hsub'
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q4;apply q5
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← q9,hvw,bOT,hwt_or]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [wq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;right;simp only [qz htb0,q0,hcov,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;left;right;simp only [qz hta0,q0,hcov,bTA];exact hon _ htc hsub'
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             right;simp only [hta0,htb0,q0,bTA]
             exact hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
lemma wj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b) :
   scanInline c s (eW rp c ws_b)=true:=by
 rw [wu]
 exact q17 hc hs htags htr (fun _ => true) (fun _ _ _ => rfl)
def ki {n:Nat}:Nat->List (BFn n × Nat)->BFn n × Nat
 | _,[] => ((fun _ => false),0)
 | 0,a::_ => a
 | k+1,_::rest => ki k rest
def yl {n:Nat}:Nat->List (BFn n × Nat)->List (BFn n × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::yl k rest
def q136 {n:Nat} (code:Nat) (ws:List (BFn n × Nat)):List (BFn n × Nat) :=
 if Nat.ble code 32 then
   let c:=Nat.sub code 1;let i:=Nat.shiftRight c 1;let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=ki i ws;let wt:=if Nat.beq ta 3 then 2 else 0
   let w:=invF a;let r:=yl i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   let rem:=Nat.sub code 33
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=ki i ws;let (b,tb):=ki j ws
   let r:=yl i (yl j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (meetF a b,wt)::r2
   else
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (joinF a b,0)::r2
def q31 {n:Nat} (xs_b:List (BFn n × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (BFn n × Nat)
 | 0,_,_ => xs_b
 | d+1,s,j =>
   let e:=q192 (PT s) j;let code:=Nat.land e 1023
   if Nat.beq code 0 then xs_b
   else q136 code (q31 xs_b PT d (Nat.add s 1) (Nat.land (Nat.shiftRight e 10) 8191))
def RgenB {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat):List (BFn n × Nat) :=
 q31 xs_b PT (Nat.sub cap s) s j
lemma q27 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   jw i (encWs rows ws)=(encL rows (ki i ws).1,(ki i ws).2):=by
 induction i generalizing ws with
 | zero => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ _ => rfl
 | succ k ih => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ t => exact ih t
lemma q28 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   q38 i (encWs rows ws)=encWs rows (yl i ws):=by
 induction i generalizing ws with
 | zero => cases ws <;> rfl
 | succ k ih => cases ws with | nil => rfl | cons p t => simp only [qy,q38,yl,ih]
lemma q153 {n:Nat} (rows:List Nat) (code:Nat) (ws:List (BFn n × Nat)) :
   q203 (2 ^ rows.length - 1) code (encWs rows ws)=encWs rows (q136 code ws):=by
 unfold q203 q136;simp only [v5]
 split
 . simp only [q27,q28];split <;> simp [encWs,q145]
 . simp only [q27,q28]
   split
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,q9]
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,qc]
lemma q119 {n:Nat} (rows:List Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (d s j:Nat) :
   q120 (2 ^ rows.length - 1) (encWs rows xs_b) PT d s j=encWs rows (q31 xs_b PT d s j):=by
 induction d generalizing s j with
 | zero => rfl
 | succ d ih => simp only [q120,q31,v5];split;rfl;rw [ih,q153]
lemma q102 {n:Nat} (rows:List Nat) (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ rows.length - 1) cap (encWs rows xs_b) PT s j=encWs rows (RgenB cap xs_b PT s j) :=
 q119 rows xs_b PT (Nat.sub cap s) s j
lemma q150 {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ (2 ^ n) - 1) cap (encTTWs n xs_b) PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 have hlen:(List.range (2 ^ n)).length=2 ^ n:=List.length_range
 simpa [encTTWs,encWs,encTT,hlen] using q102 (List.range (2 ^ n)) cap xs_b PT s j
lemma wm {n:Nat} (i:Nat) (ws:List (BFn n × Nat)):(yl i ws).Sublist ws:=by
 induction i generalizing ws with
 | zero => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons a (List.Sublist.refl t)
 | succ k ih => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons_cons a (ih t)
lemma vj {α:Type} (b:Bool) (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (if b then x::l else l):=by
 intro p hp;cases b
 . exact hl p hp
 . rcases List.mem_cons.1 hp with rfl | h'
   . exact hx
   . exact hl p h'
lemma vn {α:Type} (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (x::l):=by
 intro p hp;rcases List.mem_cons.1 hp with rfl | h';exact hx;exact hl p h'
lemma q43 {n:Nat} (code:Nat) {ws:List (BFn n × Nat)} (h:AllTagsLe3 ws) :
   AllTagsLe3 (q136 code ws):=by
 unfold q136
 have her:∀ i,AllTagsLe3 (yl i ws):=fun i p hp => h p ((wm i ws).subset hp)
 have her2:∀ i j,AllTagsLe3 (yl i (yl j ws)):=fun i j p hp => her j p ((wm i _).subset hp)
 split
 . dsimp only;split
   . exact vn _ _ (by split <;> omega) (vn _ _ (by omega) (her _))
   . exact vn _ _ (by split <;> omega) (her _)
 . dsimp only;split
   . exact vn _ _ (by split <;> omega)
       (vj _ _ _ (by omega) (vj _ _ _ (by omega) (her2 _ _)))
   . exact vn _ _ (by omega)
       (vj _ _ _ (by split <;> omega) (vj _ _ _ (by split <;> omega) (her2 _ _)))
lemma q59 {n:Nat} (cap:Nat) {xs_b:List (BFn n × Nat)} (h:AllTagsLe3 xs_b)
   (PT:Nat->Nat) (s j:Nat):AllTagsLe3 (RgenB cap xs_b PT s j):=by
 unfold RgenB;generalize Nat.sub cap s=d
 induction d generalizing s j with
 | zero => exact h
 | succ d ih => simp only [q31];split;exact h;exact q43 _ (ih _ _)
lemma q195 (T h fuel lo hi:Nat) (hlo:lo < hi):q167 T h fuel lo hi < hi:=by
 induction fuel generalizing lo hi with
 | zero => exact hlo
 | succ fuel ih =>
   simp only [q167,v5];split
   . rename_i hle;have hle':lo+2<=hi:=Eq.mp Nat.ble_eq hle
     have hdiv:Nat.div (Nat.add lo hi) 2=(lo+hi) / 2:=rfl
     have hmid_lt:Nat.div (Nat.add lo hi) 2 < hi:=by rw [hdiv];omega
     have hlo_lt_mid:lo < Nat.div (Nat.add lo hi) 2:=by rw [hdiv];omega
     split;exact ih _ hi hmid_lt;exact lt_trans (ih lo _ hlo_lt_mid) hmid_lt
   . exact hlo
lemma j8 (NN FL HT:Nat->Nat) (s h:Nat) (hne:q85 NN FL HT s h≠999999) :
   q85 NN FL HT s h < NN s:=by
 unfold q85 at hne ⊢;simp only [v5] at hne ⊢
 cases hz:Nat.beq (NN s) 0
 . rw [hz] at hne;simp only [bFT,↓reduceIte] at hne ⊢
   have hpos : 0 < NN s:=by have:=y3 hz;omega
   cases hm:Nat.beq (q205 (HT s) (q167 (HT s) h (FL s) 0 (NN s))) h
   . rw [hm] at hne;simp only [bFT,↓reduceIte] at hne;exact absurd rfl hne
   . simp only [↓reduceIte];exact q195 (HT s) h (FL s) 0 (NN s) hpos
 . rw [hz] at hne;exact absurd rfl hne
lemma q181 (a b:Nat × Nat):twEq a b=true ↔ a=b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;simp [twEq,Nat.beq_eq]
lemma q142 (x:Nat × Nat) (bs bs':List (Nat × Nat)) (h:jy x bs=some bs'):bs.Perm (x::bs'):=by
 induction bs generalizing bs' with
 | nil => simp [jy] at h
 | cons a t ih =>
   simp only [jy] at h;split at h
   . rename_i heq;cases h;rw [(q181 x a).1 heq]
   . cases he:jy x t with
     | none => rw [he] at h;cases h
     | some r => rw [he] at h;cases h;exact (lPC a (ih r he)).trans (List.Perm.swap x a r)
lemma y5 (xs ys:List (Nat × Nat)) (h:jk xs ys=true):xs.Perm ys:=by
 induction xs generalizing ys with
 | nil => cases ys with | nil => exact List.Perm.nil | cons _ _ => simp [jk] at h
 | cons a t ih =>
   simp only [jk] at h
   cases he:jy a ys with
   | none => rw [he] at h;cases h
   | some ys' => rw [he] at h;exact (lPC a (ih ys' h)).trans (q142 a ys ys' he).symm
lemma q113 (x:Nat × Nat) (xs:List (Nat × Nat)):(q62 x xs).Perm (x::xs):=by
 induction xs with | nil => exact lPR _ | cons a t ih => simp only [q62];split;exact lPR _;exact (lPC a ih).trans (List.Perm.swap x a t)
lemma q64 (xs:List (Nat × Nat)):(q125 xs).Perm xs:=by
 induction xs with | nil => exact List.Perm.nil | cons a t ih => exact (q113 a (q125 t)).trans (lPC a ih)
lemma kg {n:Nat} (rp shTT:Nat) (ws:List (BFn n × Nat)) :
   q72 shTT (encWs (allRows n rp shTT) ws)=encTTWs n ws:=by
 induction ws with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨g,tg⟩;simp only [qy,q49,q72,v5,ih]
   have hsh:=q116 (n:=n) (q106 rp shTT) g
   rw [jj rp shTT] at hsh;rw [allRows,hsh]
lemma yk {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g) (ws:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     wx g (encTTWs n ws)=encTTWs n (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 obtain ⟨π,hbij,hfix,happ⟩:=hg;refine ⟨π,hbij,hfix,?_⟩
 induction ws with | nil => rfl | cons p t ih => rcases p with ⟨h,tg⟩;simp only [q49,lMC,wx,v5,happ,ih]
lemma yv {α β:Type} {f : α->β} (hf:Function.Injective f) :
   ∀ {xs ys:List α},(xs.map f).Perm (ys.map f)->xs.Perm ys
 | [],ys,hp => by cases ys with | nil => exact List.Perm.nil | cons _ _ => exact absurd hp.length_eq (by simp)
 | x::xs,ys,hp => by
   have hmem:f x ∈ ys.map f:=hp.subset (by simp)
   obtain ⟨y,hy,heq⟩:=List.mem_map.1 hmem
   have hxy:y=x:=hf heq;subst hxy
   obtain ⟨l1,l2,rfl⟩:=List.append_of_mem hy
   have hp2:(f y::xs.map f).Perm (f y::(l1++l2).map f) :=
     hp.trans (by simpa [lMA] using (lPM (a:=f y) (l₁:=l1.map f) (l₂:=l2.map f)))
   exact (lPC y (yv hf (List.Perm.cons_inv hp2))).trans List.perm_middle.symm
lemma zv {n:Nat} (xs ys:List (BFn n × Nat)):(encTTWs n xs).Perm (encTTWs n ys) ↔ xs.Perm ys:=by
 constructor
 . intro hp
   have hinj:Function.Injective (fun p:BFn n × Nat => (encTT n p.1,p.2)):=fun ⟨_,_⟩ ⟨_,_⟩ e => by
     simp only [Prod.mk.injEq] at e;exact Prod.ext (yc e.1) e.2
   exact yv hinj hp
 . exact fun hp => hp.map _
lemma q19 {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g)
   (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q69 g ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q69;dsimp only;split
 . obtain ⟨π,hbij,hfix,hmg⟩:=yk hg ws_b;refine ⟨π,hbij,hfix,?_⟩
   have hmap_eq:∀ l,wx g l=l.map (fun p => (ym g p.1,p.2)):=fun l => by
     induction l with | nil => rfl | cons p t ih => simp [wx,v5,ih]
   have hmgp:(wx g ws).Perm (wx g (encTTWs n ws_b)):=by rw [hmap_eq,hmap_eq];exact hp.map _
   exact (q64 _).trans (hmgp.trans (by rw [hmg]))
 . exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hp⟩
lemma q20 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q35 gens ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 induction gens generalizing ws ws_b with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa [q35] using hp⟩
 | cons g rest ih =>
   obtain ⟨π1,hb1,hf1,hp1⟩:=q19 (hgens g (by simp)) ws ws_b hp
   obtain ⟨π2,hb2,hf2,hp2⟩:=ih (fun g' hm => hgens g' (List.mem_cons_of_mem g hm)) (q69 g ws) _ hp1
   exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [q35,lMMp,fCD] using hp2⟩
lemma q152 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws_b:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q186 gens (encTTWs n ws_b)).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q186;have hs0:=q64 (encTTWs n ws_b)
 cases gens with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hs0⟩
 | cons g rest =>
   cases rest with
   | nil => exact q19 (hgens g (by simp)) _ ws_b hs0
   | cons g2 rest2 =>
     obtain ⟨π1,hb1,hf1,hp1⟩:=q20 (g::g2::rest2) hgens _ ws_b hs0
     obtain ⟨π2,hb2,hf2,hp2⟩:=q20 (g::g2::rest2) hgens _ _ hp1
     exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hp2⟩
def w2 {n:Nat} (f:BFn n) (rows:List Nat) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Prop :=
 ∀ s zs_b,findFn s (encWs rows zs_b)=true ->
   ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),
     Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (zs_b.map fun p => ((fun x => p.1 (π x)),p.2)).Perm (R_bfn s j)
lemma q87 {n:Nat} (f:BFn n) (rp shTT salt:Nat) (NN FL HT:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAut1 shTT salt Rtt NN FL HT):=by
 intro s zs_b h;unfold findAut1 at h
 simp only [v5,kg,bAT,bNT,zh] at h
 obtain ⟨hne,hpeq⟩:=h;rw [hRtt] at hpeq
 exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
   by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
lemma q86 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (g0:List (Nat × Nat × Nat × Nat)) (hg0:vh f g0) (NN FL HT:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAut2 shTT salt g0 Rtt NN FL HT):=by
 intro s zs_b h;unfold findAut2 at h;simp only [v5,kg] at h
 split at h
 . rename_i h0;simp only [bAT,bNT,zh] at h0
   obtain ⟨hne,hpeq⟩:=h0;rw [hRtt] at hpeq
   exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
     by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
 . simp only [bAT,bNT,zh] at h
   obtain ⟨hne,hpeq⟩:=h;obtain ⟨π,hbij,hfix,hmg⟩:=yk hg0 zs_b
   rw [hmg] at hne hpeq;rw [hRtt] at hpeq
   exact ⟨_,j8 NN FL HT s _ hne,π,hbij,hfix,(zv _ _).1 (y5 _ _ hpeq)⟩
lemma q37 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (path:List (List (Nat × Nat × Nat × Nat))) (hpath:∀ g ∈ path,vh f g)
   (NN FL HT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutPath shTT salt path Rtt NN FL HT):=by
 have hloop:∀ p:List (List (Nat × Nat × Nat × Nat)),(∀ g ∈ p,vh f g)->∀ s (zs_b:List (BFn n × Nat)),
     vm salt Rtt NN FL HT s p (encTTWs n zs_b)=true ->
     ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
       (zs_b.map fun q => ((fun x => q.1 (π x)),q.2)).Perm (R_bfn s j):=by
   intro p;induction p with
   | nil =>
     intro _ s zs_b h
     simp only [vm,v5,bAT,bNT,zh] at h
     obtain ⟨hne,hpeq⟩:=h;rw [hRtt] at hpeq
     exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
       by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
   | cons g rest ih =>
     intro hp s zs_b h;simp only [vm,v5] at h
     split at h
     . rename_i h0;simp only [bAT,bNT,zh] at h0
       obtain ⟨hne,hpeq⟩:=h0;rw [hRtt] at hpeq
       exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
         by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
     . obtain ⟨π1,hb1,hf1,hmg⟩:=yk (hp g (by simp)) zs_b;rw [hmg] at h
       obtain ⟨j,hj,π2,hb2,hf2,hperm⟩:=ih (fun g' hm => hp g' (List.mem_cons_of_mem g hm)) s _ h
       exact ⟨j,hj,π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hperm⟩
 intro s zs_b h;unfold findAutPath at h;rw [kg] at h;exact hloop path hpath s zs_b h
lemma q55 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (gens:List (List (Nat × Nat × Nat × Nat))) (hgens:∀ g ∈ gens,vh f g)
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (haut:∀ k,vh f (aut k))
   (NN FL HT PT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutGen shTT salt gens aut Rtt NN FL HT PT):=by
 intro s zs_b h;unfold findAutGen at h;simp only [v5,kg] at h
 split at h;· cases h
 . rename_i hne_b
   have hne:=y3 (Bool.eq_false_iff.2 hne_b)
   set j:=q85 NN FL HT s (q75 salt (q186 gens (encTTWs n zs_b)))
   have hj:j < NN s:=j8 NN FL HT s _ hne
   set aidx:=Nat.shiftRight (q192 (PT s) j) 23
   obtain ⟨π1,hb1,hf1,hori⟩:=q152 gens hgens zs_b
   obtain ⟨π2,hb2,hf2,hmg⟩:=yk (haut aidx) (R_bfn s j)
   rw [hRtt,hmg] at h
   have hperm_b:=(zv _ _).1 (hori.symm.trans (y5 _ _ h))
   obtain ⟨π2_inv,hleft,hright⟩:=Function.bijective_iff_has_inverse.1 hb2
   have hinv_bij:Function.Bijective π2_inv:=Function.bijective_iff_has_inverse.2 ⟨π2,hright,hleft⟩
   have hinv_fix:∀ x,f (π2_inv x)=f x:=fun x => by have:=hf2 (π2_inv x);rw [hright x] at this;exact this.symm
   refine ⟨j,hj,π1 ∘ π2_inv,hb1.comp hinv_bij,fun x => by simp [hf1,hinv_fix],?_⟩
   have hmap_inv:=hperm_b.map (fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2))
   have hrhs:(((R_bfn s j).map fun p => ((fun x => p.1 (π2 x)),p.2)).map fun p => ((fun x => p.1 (π2_inv x)),p.2))=R_bfn s j:=by
     rw [lMMp]
     have hfg:((fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2)) ∘ fun p:BFn n × Nat => ((fun x => p.1 (π2 x)),p.2))=id:=by
       funext ⟨g,tg⟩;simp only [fCD,id];congr 1;funext x;exact congrArg g (hright x)
     rw [hfg,List.map_id]
   rw [hrhs] at hmap_inv
   simpa [lMMp,fCD] using hmap_inv
lemma span_sound (P:Nat->Bool) (len start:Nat) (h:span P len start=true) :
   ∀ i,start<=i->i < start+len->P i=true:=by
 induction len generalizing start with
 | zero => intro i h1 h2;omega
 | succ m ih =>
   simp only [span,bAT] at h;intro i h1 h2
   by_cases heq:i=start
   . subst heq;exact h.1
   . exact ih (start+1) h.2 i (by omega) (by omega)
lemma q179 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (cap:Nat) (hcap:cap<=11) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (R:Nat->Nat->List (Nat × Nat))
   (hR:∀ s j,R s j=eW rp c (R_bfn s j))
   (hTags:∀ s j,AllTagsLe3 (R_bfn s j))
   (findFn:Nat->List (Nat × Nat)->Bool)
   (hFind:w2 f (aR n rp c) NN R_bfn findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true) :
   ∀ s ≤ cap,∀ i < NN s,
     ¬ TR f s (R_bfn s i):=by
 intro s;induction s with
 | zero =>
   intro _ i hi htr;have hb:=hBar 0 (nZL cap) i hi;obtain ⟨tg,heq⟩:=htr.inv_zero
   simp only [bar,hR,heq,encWs,lMC,List.map_nil,hc.goalv_eq,q0] at hb;cases hb
 | succ s ih =>
   intro hs i hi htr
   have hih:=ih (by omega)
   have hb:=hBar (s+1) hs i hi
   simp only [bar,v8] at hb
   have hscan_false:scanAll c s (R (s+1) i)
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=false:=by simpa using hb
   have hscan_true:scanAll c s (eW rp c (R_bfn (s+1) i))
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=true:=by
     apply q17 hc (by omega:s<=10) (hTags (s+1) i) htr
     intro zs_b hzt htr_z
     have hnf:findFn s (eW rp c zs_b)=false:=by
       cases hf:findFn s (eW rp c zs_b)
       . rfl
       . exfalso;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s zs_b hf
         exact hih j hj (TagRun.perm hperm (wp π hbij hfix htr_z))
     simp only [hnf,bNF,bTA]
     cases s with
     | zero => rfl
     | succ s' =>
       simp only [q2 (Nat.succ_ne_zero s'),Bool.false_or]
       exact wj hc (by omega:s'<=10) hzt htr_z
   rw [hR,hscan_true] at hscan_false;cases hscan_false
def checkGenList (n:Nat) (f:BFn n):List (List (Nat × Nat × Nat × Nat))->List (List (Nat × Nat))->Bool
 | [],[] => true
 | sw::sws,ps::pss =>
   kq n ps&&(q163 n ps==sw)&&(ym sw (encTT n f)==encTT n f)&&checkGenList n f sws pss
 | _,_ => false
lemma ye (n:Nat) (f:BFn n) (gsw:List (List (Nat × Nat × Nat × Nat)))
   (gsp:List (List (Nat × Nat))) (h:checkGenList n f gsw gsp=true) :
   ∀ sw ∈ gsw,vh f sw:=by
 induction gsw generalizing gsp with
 | nil => intro _ hm;cases hm
 | cons sw sws ih =>
   cases gsp with
   | nil => simp [checkGenList] at h
   | cons ps pss =>
     simp only [checkGenList,bAT,beq_iff_eq] at h
     obtain ⟨⟨⟨hv,hmk⟩,hfix⟩,hrest⟩:=h
     intro g hg;rcases List.mem_cons.1 hg with rfl | hg2
     . rw [← hmk] at hfix ⊢;exact kw f ps hv hfix
     . exact ih pss hrest g hg2
def checkAutFn (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat))):Bool :=
 (List.range autp.length).all fun i =>
   let ps:=autp.getD i []
   kq n ps&&(q163 n ps==aut i)&&(ym (aut i) (encTT n f)==encTT n f)
lemma q58 (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat))
   (autp:List (List (Nat × Nat))) (h:checkAutFn n f aut autp=true) (hdef:∀ i ≥ autp.length,aut i=[]) :
   ∀ i,vh f (aut i):=by
 intro i;by_cases hi:i < autp.length
 . have h1:=List.all_eq_true.1 h i (List.mem_range.2 hi)
   simp only [bAT,beq_iff_eq] at h1
   obtain ⟨⟨hv,hmk⟩,hfix⟩:=h1;rw [← hmk] at hfix ⊢;exact kw f (autp.getD i []) hv hfix
 . rw [hdef i (by omega)];exact q138 f
def w8 (n:Nat) (f:BFn n):Bool :=
 let t:=encTT n f;!(Nat.beq t 0)&&!(Nat.beq t (2 ^ (2 ^ n) - 1))
lemma ju (n:Nat) (f:BFn n) (h:w8 n f=true) :
   ∃ y y':Fin n->Bool,f y≠f y':=by
 unfold w8 at h;simp only [bAT,bNT,zh] at h
 obtain ⟨hne0,hne1⟩:=h
 have hex1:∃ r < 2 ^ n,f (q1 n r)=true:=by
   by_contra hall;push Not at hall;apply hne0;apply nEQ;intro r
   rw [vr,nZT];split;exact Bool.eq_false_iff.2 (hall r ‹_›);rfl
 have hex0:∃ r < 2 ^ n,f (q1 n r)=false:=by
   by_contra hall;push Not at hall;apply hne1;apply nEQ;intro r
   rw [vr,nTB];split
   . rename_i hr;have:f (q1 n r)=true:=by cases hf:f (q1 n r);exact absurd hf (hall r hr);rfl
     simp [hr,this]
   . rename_i hr;simp [hr]
 obtain ⟨r1,_,h1⟩:=hex1;obtain ⟨r0,_,h0⟩:=hex0
 exact ⟨q1 n r1,q1 n r0,by rw [h1,h0];decide⟩
def q77 (n:Nat) (f:BFn n):Bool :=
 (List.finRange n).all fun v =>
   (List.range (2 ^ n)).any fun r => let x:=q1 n r;f (Function.update x v (!x v))!=f x
lemma q44 (n:Nat) (f:BFn n) (h:q77 n f=true) :
   ∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x:=by
 intro v;have h1:=List.all_eq_true.1 h v (List.mem_finRange v)
 obtain ⟨r,_,hr⟩:=List.any_eq_true.1 h1;exact ⟨q1 n r,bne_iff_ne.1 hr⟩
def q147 (c:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (xs:List (Nat × Nat)) (s0:Nat):Bool :=
 findFn s0 xs||!(Nat.beq s0 0||scanInline c (Nat.sub s0 1) xs)
def verifyBase (n cap:Nat) (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Bool :=
 let rows:=aR n rp c
 let xs_b:=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 Nat.ble cap 11&&w3 n f rp c&&w8 n f&&q77 n f &&
 ((List.finRange n).all fun i => Nat.ble (initTags i) 3) &&
 (xs==encWs rows xs_b)&&(xstt==encTTWs n xs_b) &&
 ((List.range (cap+1)).all fun s0 => Nat.blt (Nat.add s0 1) n||q147 c findFn xs s0)
lemma prove_base {n cap:Nat} (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (NN PT:Nat->Nat) (findFn:Nat->List (Nat × Nat)->Bool)
   (hBase:verifyBase n cap f rp c initTags xs xstt findFn=true)
   (hFind:w2 f (aR n rp c) NN
     (RgenB cap (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)) PT) findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 unfold verifyBase at hBase
 simp only [bAT,Nat.ble_eq,beq_iff_eq] at hBase
 rcases hBase with ⟨⟨⟨⟨⟨⟨⟨hcap,hcfg_b⟩,hnc_b⟩,hdep_b⟩,htags_b⟩,hxs⟩,hxstt⟩,hroots⟩
 have hc:=jn n f rp c hcfg_b
 have hnc:=ju n f hnc_b
 have hdep:=q44 n f hdep_b
 set xs_b:List (BFn n × Nat):=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 have hTags_xs:AllTagsLe3 xs_b:=fun p hp => by
   rw [List.mem_ofFn] at hp;obtain ⟨i,rfl⟩:=hp
   exact Eq.mp Nat.ble_eq (List.all_eq_true.1 htags_b i (List.mem_finRange i))
 have hlen_rows:=zl n rp c.shTT
 have hR:∀ s j,Rgen c.all1v cap xs PT s j=eW rp c (RgenB cap xs_b PT s j):=fun s j => by
   rw [hxs,hc.all1v_eq,← hlen_rows,q102]
 have hNoRun:=q179 hc cap hcap NN (RgenB cap xs_b PT) (Rgen c.all1v cap xs PT) hR
   (fun s j => q59 cap hTags_xs PT s j) findFn hFind hBar
 intro t hcirc;by_contra hlt;have hle:t<=cap:=by omega
 obtain ⟨s0,hs0,htr⟩:=q88 f cap initTags hnc hdep htag t hle hcirc
 have hroot:=List.all_eq_true.1 hroots s0 (List.mem_range.2 (by omega))
 simp only [bOT] at hroot
 rcases hroot with hlen_small | hchk
 . have hlt_n:s0+1 < n:=by simpa [Nat.blt_eq,v8] using hlen_small
   have htr_len:n<=s0+1:=by simpa using htr.len_le
   omega
 . unfold q147 at hchk;simp only [bOT] at hchk
   rcases hchk with hfound | hkill
   . rw [hxs] at hfound;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s0 xs_b hfound
     exact hNoRun s0 hs0 j hj (TagRun.perm hperm (wp π hbij hfix htr))
   . simp only [bNT,Bool.or_eq_false_iff,zh] at hkill
     obtain ⟨hs0_nz,hinl_f⟩:=hkill
     cases s0 with
     | zero => exact hs0_nz rfl
     | succ s' =>
       rw [hxs] at hinl_f;have hinl_t:=wj hc (by omega:s'<=10) hTags_xs htr
       change scanInline c s' (eW rp c xs_b)=false at hinl_f
       rw [hinl_t] at hinl_f;cases hinl_f
lemma Rgen_encTTWs_eq {n all1tt cap:Nat} (hall:all1tt=2 ^ 2 ^ n - 1)
   (xs_b:List (BFn n × Nat)) (xstt:List (Nat × Nat)) (hxs:xstt=encTTWs n xs_b)
   (PT:Nat->Nat) (s j:Nat) :
   Rgen all1tt cap xstt PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 rw [hall,hxs];exact q150 cap xs_b PT s j
lemma q196 {c:Cfg} {findFn:Nat->List (Nat × Nat)->Bool} {R:Nat->Nat->List (Nat × Nat)}
   {cap:Nat} {NN:Nat->Nat}
   (h:∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true) :
   ∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true:=h
lemma span_all_sound {P:Nat->Nat->Bool} {cap:Nat} {NN:Nat->Nat}
   (h:(List.range (cap+1)).all (fun s => span (P s) (NN s) 0)=true) :
   ∀ s ≤ cap,∀ i < NN s,P s i=true:=fun s hs i hi =>
 span_sound (P s) (NN s) 0 (List.all_eq_true.1 h s (List.mem_range.2 (by omega))) i (nZL _) (by omega)
lemma span_chunk_join {P:Nat->Bool} {a b:Nat}
   (h1:span P a 0=true) (h2:span P (b - a) a=true) :
   ∀ i < b,P i=true:=fun i hi => by
 by_cases h:i < a
 . exact span_sound P a 0 h1 i (nZL _) (by omega)
 . exact span_sound P (b - a) a h2 i (by omega) (by omega)
lemma span_chunk3 {P:Nat->Bool} {a b d:Nat}
   (h1:span P a 0=true) (h2:span P b a=true) (h3:span P (d - (a+b)) (a+b)=true) :
   ∀ i < d,P i=true:=fun i hi => by
 by_cases h1i:i < a
 . exact span_sound P a 0 h1 i (nZL _) (by omega)
 . by_cases h2i:i < a+b
   . exact span_sound P b a h2 i (by omega) (by omega)
   . exact span_sound P (d - (a+b)) (a+b) h3 i (by omega) (by omega)
lemma span_chunk4 {P:Nat->Bool} {a b d e:Nat}
   (h1:span P a 0=true) (h2:span P b a=true) (h3:span P d (a+b)=true)
   (h4:span P (e - (a+b+d)) (a+b+d)=true) :
   ∀ i < e,P i=true:=fun i hi => by
 by_cases h1i:i < a
 . exact span_sound P a 0 h1 i (nZL _) (by omega)
 . by_cases h2i:i < a+b
   . exact span_sound P b a h2 i (by omega) (by omega)
   . by_cases h3i:i < a+b+d
     . exact span_sound P d (a+b) h3 i (by omega) (by omega)
     . exact span_sound P (e - (a+b+d)) (a+b+d) h4 i (by omega) (by omega)
lemma fun_eq_of_encTT {n:Nat} (f g:BFn n) (h:Nat.beq (encTT n f) (encTT n g)=true):f=g :=
 yc (Eq.mp Nat.beq_eq h)
lemma prove_base1 {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAut1 c.shTT salt (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAut1 c.shTT salt (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q87 f rp c.shTT salt NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_base2 {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (g0:List (Nat × Nat × Nat × Nat)) (g0p:List (Nat × Nat))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hg0:checkGenList n f [g0] [g0p]=true)
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAut2 c.shTT salt g0 (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAut2 c.shTT salt g0 (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q86 f rp c.shTT salt g0 (ye n f [g0] [g0p] hg0 g0 (by simp))
     NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_basePath {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw path:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (hsub:path.all (fun g => gsw.contains g)=true)
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutPath c.shTT salt path (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutPath c.shTT salt path (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 have hg:=ye n f gsw gsp hgen
 have hp:∀ g ∈ path,vh f g:=fun g hgp =>
   hg g (List.contains_iff_mem.1 (List.all_eq_true.1 hsub g hgp))
 exact prove_base f rp c initTags xs xstt NN PT _ hBase
   (q37 f rp c.shTT salt path hp NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_baseGen {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (haut:checkAutFn n f aut autp=true)
   (hdef:∀ i ≥ autp.length,aut i=[])
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q55 f rp c.shTT salt gsw (ye n f gsw gsp hgen)
     aut (q58 n f aut autp haut hdef) NN FL HT PT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
structure BaseEntry where
 k:Nat
 E:List (Fin k × Fin k)
 lb:Nat
def BaseTableOk (bs:List BaseEntry):Prop :=
 ∀ b ∈ bs,∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s
def q61 {n:Nat}:List (Fin n)->Bool
 | [] => true
 | a::t => !t.contains a&&q61 t
lemma q83 {n:Nat} (l:List (Fin n)) (h:q61 l=true):l.Nodup:=by
 induction l with
 | nil => exact List.nodup_nil
 | cons a t ih =>
   simp only [q61,bAT,bNT] at h
   exact List.nodup_cons.2 ⟨by simpa [List.contains_eq_mem] using h.1,ih h.2⟩
def fm15419:BFn 7:=fun x => Nat.testBit 312082526752096706374802891772260253696 ((if x 0 then 1 else 0)+(if x 1 then 2 else 0)+(if x 2 then 4 else 0)+(if x 3 then 8 else 0)+(if x 4 then 16 else 0)+(if x 5 then 32 else 0)+(if x 6 then 64 else 0))
def rm15419:=0xa546e59ad4f666e38eceed9a6d59adb7161f966b63a91b4e3b35a943cd8eb53d99b8d9a7bb669b55a9edc58766edb8ec49cd8eb59a30f4e3b34f666a3669eed9a6956a7b7161b966b63a32736ead66a52d3b71d6a54766edb4e951b966b53d99b8e3b3bb669b566b6dc587e59ad8ea46d38ecd6a50f363ad4f666e3669eed9a6d56a7b7161d9bb6e3b127363ad668c3d38ecd3d99a8d9a7bb669a55a9edc586e59ad8e8c9cdbab59a94b4edc75a951d9bb6d3ddb71d9ad4f76dc766b53ddb71d9ad4f76dc766b53ddb71d9ad4f76dc766b53ddb71d9ad4ff7dfdefcfdefdbb73f3cf76dddafcedd7db767db9f1e3bd76f5bb376bd6ad4ecd3df7f75edb775dbb39ebd6c74fffefbefcf7edcf7eedbaf3e3bf7aedbb35eb53f9f3e7cf9f3d7af5ebd7aebd7af5ebd74e9d3a74e9cd9b366cd9a7cf9f3e7cf7efdfbf7effe7cf5ebc75ebd3972e3c766cd5ab4e9d39b366cb97161b972d5ab156ad4a54a8d19f3e74e9b365cb931e3c6870dfbe7aedcb76ccd7ae5aad3a33e78e9b325cb13
def xm15419:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa54e5553953934d5fce4d5c4e4d539554e54e4d357f39357139375d75d75d7579d79f5e7cfeef6fbd000fff03ffc18c38d063cfeef6fbd,0),(0xcccccccccccccccccccccccccccccccc8d52a357f4ce94e5533a339396354a8d5fd33a53954ce8ce4e5aebaebaebaecf6cf7b3df37f5f7d703f000ffffcc30c7230cf37f5f7d7,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f02b18cac4ac6538a03194a3a538ac632b12b194e280c6528e94ecb2cb2cb2cb9e397ce78fc739bae6fc0fc0fffff1c307cc70fc739bae6,0),(0xff00ff00ff00ff00ff00ff00ff00ff00323f4c2809793b12a5c4c54c38c8fd30a025e4ec4a97131530ed34d34d34d3f0bfa8fc2ff83e3cf8fff03f03fffe03f80f80ff83e3cf8,0),(0xffff0000ffff0000ffff0000ffff0000fca38e8e338e0238ce38e8f1c7f28e3a38ce3808e338e3a3c711c71c71c71fffc240fff55b7fc0ffffffc0000ffffc000fff0003fc0ff,0),(0xffffffff00000000ffffffff0000000003dc7930ce71fcc331c7130e380f71e4c339c7f30cc71c4c38ee38e38e38e3ffffff000aa4bfff00fffffffc0ffffffff0000003fff00,0),(0xffffffffffffffff0000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03ffffffffffffc00000,0)]
def xtm15419:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0),(0xcccccccccccccccccccccccccccccccc,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0),(0xffff0000ffff0000ffff0000ffff0000,0),(0xffffffff00000000ffffffff00000000,0),(0xffffffffffffffff0000000000000000,0)]
def cm15419:Cfg:=⟨116,232,334,436,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xeac8e888eac8000000000000000000001c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c7fffffffffffffffffffffffffffff00000000000000000000000000000,0xfffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffff,0x1041041041041041041041041,0x1d75d75d75d75d75d75d75d75d,0x20820820820820820820820820,0x1041041041041041041041041,0x2082082082082082082082082,0x1d75d75d75d75d75d75d75d75d,0x20820820820820820820820820⟩
def Nm15419:Nat->Nat
 | 5=>28
 | 6=>344
 | 7=>1381
 | 8=>1098
 | 9=>64
 | 10=>1
 | _=>0
def Lm15419:Nat->Nat
 | 5=>6
 | 6=>10
 | 7=>12
 | 8=>12
 | 9=>8
 | 10=>2
 | _=>0
def Hm15419:Nat->Nat
 | 5=>0xf584dbf24d43e8fac2e597e0e56639dae400d838bdd4bbc3cbd759c2b4b7bbb8b7b31b3eaf62fda20d5b974667943a258916cd815b3573f20f6cf60f641b146139b44b9ef442edbd345a882790720ef3220d0944
 | 6=>0xffd80cfef05afecc2ffd8392fba7c3faf0a4fa8cdefa6909f9372df70f6ef7013ef5ce67f58acdf530c7f3e82af3bb9bf3977bf34f72f0da02efc738edbee4ecd26dec619debd3e2eb02e6ea8c1bea875ee9b40ae90cfbe7ff8ce6e29ce6731ae5f586e42c3ae3af11e378d9e283f1e17683e16c76e163b2de6424dd8affdbc6fedbadccda22d5d9ba15d99568d83254d8316dd8138ed6682ad5939ad17bf7d1638cd15e96cff3e6cfafb6cf8e1fcf8255ce4582ce1171cdd6d9cd7efbcd33a9cc8457cbb029cbad08c9821cc8aa15c81921c5d2a6c545c3c4faddc41162c3d3cec11459c0ff03bfb60bbf2f4ebc7839bc5e96bbd3dbbba1f6bab77cba2bb0b98c44b8b4ccb75233b5f829b49c9cb423d2b41f8eb3b52cb338a1b3067fb296a4b24b52b0afd0b0a78facb891ac6d36abfa0dab0134aafbdfaa537da9e878a9beafa99d39a857b1a6b75da4bd2aa4b82aa3c7c5a1ac7da1763fa13741a105d3a048b29fd55b9f18969e40999e31269e2cd19e0d539e01f79acc61997e97993b6d99395b99174297cea595fa99957d2e93fa8e93a2b091d59b91d2399164de9111b69038ed8fe4298f5abb8f55bb8e23f98dc2588d9a858b5ac58aaed4891f3f88c763885046883416881c27871a7585605b855e8c84f8d184980583c1d983b4d3829bee82944c82824b824a9f823acc80cb7780b1d47f82da7f322b7f2c877f18887e84077e5a247e17f57dc4d27d34c37c6fca7b5ff67b3c2378dbec78345177edce77da1476e7ca75c07175b6c975ac3e754eba74fbd274b5a874a5497494487476b3746f017377a073103f721dc2704d4b6f9faf6eb3ff6e68716e0b356d11336cf7906b69086b52c86afb6d69fed469fe1569b81568794d67abf567446b66a0526373e36329fe627457615cb0608ac05f71bd5f06515e94d45e15125d3c065c93075b1ecf5aeadc5ab8db586b2a562406555c1a52ed585237395112b350bdae5096c75055ee4fc8f04f7de74f6e7e4f3f124f27da4ee7af4db0df4d83b44d11e848fdd747e6f44703a446f8fb46ba86464918463eab45e44345e27f45e14745bf7d448966440efc41522940fb0c40d1e73fd7c23ec3303df1c33c83713c7e713c410c3abe233abb8e3a3d073963a9369be4361af035f83a35c5a135c3dd35c2a535bbb03537e9351e4631378f31272330dd8930cab830ae583012502fed0a2f6ae32f3bb42da86c2ccfd32cb8072c64cf2c5fcf2a5d7929ec6529785e286366278d882637f725957224b9bd23c4fb231b6722e67e222baf2117de20f51f20bee7203fd7203e9f1ccc161bab9f1a0874199e6d1913d51844c4182f4816eb9316922b13b45613b1af1300d811caed11c5ed103ce6102127100ab70ed8d50e628c0d840f0b78f40b5b960b3ae10a72170a6d17097cb206820806250504bad1034fcd02e23600a79f
 | 7=>0xffc843ff9535ff9035ff3a17ff38a0ff379dff3665ff09abfeea96fed8aafeadd1fead5bfe9fd0fe0452fd9f54fd977ffcd7e2fc8a1dfc65a8fc4d4ffc4b7bfc40d5fbd25bfba18ffb8f3ffb544efae822fad438fab3b9fa8fd8fa87befa6b5dfa26fafa01f7f9fd4af9e233f983d7f9313df8d4d0f8ccdbf85bb7f82cd3f80389f782dff760c6f7601ef7325df731fbf716d8f711f5f6fc64f6e84cf6b423f66977f6613bf64a84f63f37f62090f60802f5c77af5bfc4f58b99f55071f4c632f4aebbf490c4f45019f4275bf422b2f41fcbf41378f3ef4df3bbe3f3b9adf33971f332c2f32daaf3036ff2ef13f2df0ef2de1df2a6b0f28254f2679df266f6f255caf215a2f1cdd6f142b5f0cc86f0bf60f052c4f01f1ff01aacefc1dbefbb6def6ebeef4109ef3fb4eeee4fee5ef4ee532bee2a10ee1abfedfed3edeaf6ed9789ed7efbed6303ed5d9bece0a2ec9b7bec7d3aec2233ebe409ebc712eba777eba70aeb7fa7eb5736eb36f3eb2b50eb2955eb1e65eb0bc6eae20eeac81ceabe38ea32c6ea32a7ea2dc6ea2692e9fc69e9d7a8e9d631e9d52ee9d3f6e9b397e9a939e97acae8f858e8cedce894bee87fafe87290e86634e83d0ce80dc0e80d46e78768e74457e7285ee68ddbe6877be5da77e5c297e5bd24e5bc07e5a69ee5a379e557e7e47913e4617ee449cce42404e40a00e3eb90e3e0d4e3c090e3a682e380d3e3210be2e2c6e2e189e2ca64e2b028e277e2e1fe57e1af86e1af1be129a5e12427e10cb0e064ece00d6be00c33dfee02df884ddf2e55df0888def10ddeb556de8cdede3cf4de3bbcddeb56ddd7c7ddd702ddcf27dd8f65dd8ca4dd8931dd8689dd680bdd34cadd22aadd1d55dce72adca3a8dca270dca003dc9c77dc986fdc8d14dc5de1dc3785dbae13dba318db5633db2f0bdb1cf8da9fb1da8d6ad98be0d9544dd924ead91b42d8eb16d8e9ded8c40fd8a148d88887d86c2ad81fa8d80cced7f8aad77cf5d71228d69e2dd69bb3d66d13d65a5ed63752d508e3d4d038d4c404d472d3d458aad446cad4394fd4040dd3ac61d39ee8d2ff2cd2eecdd2c037d2bf50d2846fd232e4d22c7dd1dbead1dac7d1ac63d12c3fd102c0d10188d0ff16d0b3f8d081f9d075ded07582d06014d02ff5cff578cf6adacf10adcedef5ceadf6cea791ce8f9dce8921ce8440ce43f4ce3ba5ce333cce2402cdedc1cde685cd7efbcd49dbcd07c2ccdd7fccb1f5cc82cccc6b60cc6417cc495ccc288bcc2828cbac09cb0875cacfc2ca9ae9ca82b0ca8178c9c24bc937fec90b0cc90a3fc8e141c8da85c8d94dc8b9d6c8601fc85c60c84799c7f888c7a0cdc79eb2c77ef4c745afc74335c741fdc71b96c718b2c710cac6eb3dc6e95fc6d202c6b0bcc665acc62811c603cdc5f3c4c5e3c0c5ae7dc5775cc572bec53fb4c53e67c52afbc5239fc5170bc4e045c49064c45bf3c3e620c3c286c2e1bdc29254c28cd9c27104c2476ac1f20fc1ca60c19254c13c8ac13944c0f71cc0f1bfc0b72dc0b38dc0acc6c076f3c03b50bf6c13bf64febf5d21bf2072bf0ae1bed8aebed444be9b33be73c6be633bbe0828bdbb41bdb20cbd918dbd8c90bd71a9bd5c09bcf933bc797bbc7839bc5e96bc3a02bc367ebbff5cbbfdcabbc749bbc59ebba2acbba032bb9efabb8539bb5aefbb4529bb4509bb081ebaf997bae9eebae8efbacd86ba7da4ba7d88ba18e5b9de5cb95dc2b93159b90feab8d61db88b52b7dc9fb7ad41b79a59b77dd6b76d52b7666ab74ddcb6b903b68de5b5f973b5e003b5d33eb5a9dfb595f3b57dbab5387ab4aa58b46f21b46b3cb46531b43089b3dd3eb3d58fb3d2ceb3a82db3a59eb3a512b2c86bb2c77db278f6b241aab23e3fb1fd8ab1eac7b1d7b6b1cc15b1b906b1b643b186f0b146e7b136dcb1033db0565cb02732afdd45afcccdafbe41afb49cafa206af57a8af354caf2b30af07dbaed538ae5c68adf049adc76badc633ad8896ad50bead4fb4acdffbac9945ac8febac06e1ac0463abfa0dabcd38ab94adab7e67ab68d6ab1e14ab1484ab080eaad96eaa9c9faa1bf5aa0e0eaa09a4a9bfbaa99395a98cefa9075fa8bc8ba88dc4a85bbfa857c5a8511ca7b688a75f48a747d1a69ceda69b3ca680a5a48fd0a45d4aa44147a40f0ba3f42ba3af2aa39306a35876a32350a3128ca30928a2d2eaa29be7a25768a1dbafa1a55da0d9e7a05ad5a03384a02750a0137c9fbfbc9f64a09f05509eaa309e6e549d9b739d4c189d38569d25bb9cea1d9caf2d9c9e579c957f9c90c89c75479c6fd19c2bc59bda7b9b7f5d9b7bab9af3ed9af2a19a8a909a74e59a74989a09e799ea6799e9a899d2dd99c45999237698d75998c27598beef987672986a8398580297ee4f97db0597d48597cdb197b4d997a113979bc8973a3796bd1a9684c39627799618f595fb7595f1c89562d49508b394ebfc94db45946bd09451c2943bb494053493ef8993eedb93909c93578892be2692a96692a82e92a68192a06a928fca92103d91d0df9195b7912b61911e3690d60a90ba2f90787c903fc68fb01e8f7eb78f5bb38f48b58f34598f270d8f244a8f1f478ef9dc8ef7dc8ec79a8ea7f08ea4568e60028e368e8e30978def888dc2678dbcfa8dbb368da6b98d87fb8d3cb28d25888d25088ceec28cd7798cadb38c980a8c8cab8c59e78bf1f08be1748b08258b018b8ac9398a91de8a91c08a6f568a43a98a09d58a008c8a005a8936318881e488733288395e87e9a987db8587b918877a9087583e87510c87037e87024686bd0686a22d8677ed86557c86485c861a0a85984285206a84c87883def683db2b8394ce83814783725c82ec7e82745d825a3382217f821501820e7f8194418158f38157878149f181225480be5780b56b80a6c4807a588075338051088014217fdd3e7fc3ca7f4b0b7f086b7ee60f7ed9d87ec4237eb7bc7e64ca7e34e77e2d3d7dcefb7da4707da18b7d696d7d4b2f7d347f7d28ec7cbca17cb7b67c14b17bd1147bb9a87ba16f7b97a47b7d3c7b739b7b613b7aff2a7add577ad80d7ad21e7aa9427a94837a6dd97a37c87a204d7a1aef79f94479e63379837d794cb779281d79001e78634b7837ac7828cd78223077fecb779b7977964677750a77623e775d5976946276917d768f81765e8176435f76387375f167759993757b08755c56753517752c2574d44b74cc0a74682b7445e4742b6a7427ee74274473e84973abd7738ad5737a04733a947338f07310c372d6ef72d466729fa471fe8871f5cf71e14e71b98871a3f7714e2970ffe470bf1570a5e36ff0eb6fdfc56fbe386fb1396f9ca66f7d206ef7ac6edb0f6eb04c6eab4f6e96e06e89fd6e543b6e074e6de8786d5f806d35406d22596ce6086cdfd56cdad86ccf826cc9e16cc73f6cbef16cac106c96c46c753b6b87b56b37196b17e96b14c06b09cb6b07b56aff0b6aee996aee7a6ab3856a615b6a3c5b69a51a69846569552e6923fe68ea1168de1268d27868cace689289688a946875756816d067c67d677fff670737666ea566573966353565c9176563786557b0654f85650f3a64e8b364d08e64a9b56486c2646e896428c7640e0f63f8a0636fa2635df8631c4962d6f762d51e61bf0c618ff2617cc5615239614bd26131f3612f0e61068060e816609be56070b25fffe25fba185f71bd5ee62a5ee2a45ea2dc5e93235e21905dfeba5de9a15dd8255d15b35d09fa5cfc735cf4115cf2175cab405c825f5c3a805c2e435c1f2a5ba2675b7c675b21a05aed175ae4c45a94f75a79625a18ed5a115f5a054d59b4ad58d54758bed9587bc4587a8c584e4357ca7f57ac0a5780b1577d6657786957771c5734365704d056dc6556d47756b39d567fce56657d56356755b32255a546559c9c558c0b5555305534fd54fd2f54e5f654dbdc54d9ec54bd0e54add554842a5472bf53abb053932253146652a248528dba5266d851f9d951f8a651db3951aa765198f651434651308d50dc4350db97509de25083b05041ed50282f4fea584fdb7f4faccb4f63d64ef40f4ee51c4e96314e16c34daf534d84214c9ba24c837d4c74034c65954c5c9d4c2d834c11604be9634ba44a4ba4114b5b8b4b12c54b09784b03994aff114aee884a4cc14a40e94a358f4a345149eb4949965d4996044994fa495b6f48f3444887324873ff48114647d24747c3ad47ae1c4785124775c747463847344d46cbd446407f464017463bba4619d946095545f4bf45790c4575c1455f6945427c453484452c1d4515874501d144fc0744ac3844a10544734d44403944153543ec2c43c82543c0d343ae8943a6214376ce42ef9e42c3424286dd425bfa424c19421a4241f7ae41f4c941de1241b85d4190f24177f3411f2740f7f940cfa4406222405731405610403e7b402e2a3fe6593fc5693fbe9e3fa6593f87d83f4e6e3ea6ba3e47d63e20f53d8f4f3d78183d3fd93cdfa43cd6433cd2c33ca5d03c99a23c78ca3c32dc3be6523b8e153b462c3b024c3ac5c03a9d7c3a78f13a4b8e3a18343a13a639bd9e3998f739918139915e39820539344f38ea35389922386fcb38223d37e175371532371194370f6936abc336a6ef369f54367bd8367af1365baa3651c6362eee36217536099f359ca23590363568bc34fae034ee5234de7a34bd7a34bbb834ba9534b87a349d483433ee34303c33f8e133586733240e33134d330d8832fcf132cd933299af3247f331f65f31c58331c05e31bb7d3144d93136f230eda330dd8930ce8c308fd9303d8630312f3013523004162ffcdb2fa3292f74622f667b2eed742eda4b2e882c2e70b52e3d6a2dec892dcfaa2dcbd92db6de2d60d32d42582d1ad22ccf112cbdc22cb7b52caf1f2ca11e2ca03e2c953f2c925a2c7f492c7ba32c171a2bddc92bbcb82bb8ba2b3dea2afdef2af0782ad5092ac1e32a815a2a29c62a12c629f68c299e6f295dd1292d782914fd28f00f28b0e32880fd28771a28594f2854be2773d427704a27519d26db7126b08626a4f02683e326503626479325aea4259fdd256c562540b925133e24e91f24ddfd24620623d85423a5d5239d84238f47237bf3231fb822bc1822a53b229782226ce822167c21edec2177cf2165b021474a213ce5210dbe20ef5720bee720b3ed209d6f209c711f98521f82031f6b7d1f5c881f5aec1f1f481f134d1e9f791e9e411e5a471dc5131d8f371d86bd1ce3e41cbf9e1c93f01c92a41c3e341c15871bb1961b280c1afd9b1ac1bd1ab0c51a929d1a7a2d1a11f31a040c19e9b619e87e196e32192f1a191eab188ed918651218438c1840281836ac17feee17c282179b17173dcf17176417162c16d9c916b4ab16603515fc6415c8c315b84415a6051591fd1572f215416915148415110114828014133f14093b13cb0913878713520a134e74130aa912d9a812a3c712439511baa41185421182251180b1114e1710e524109ab5106c8a105d961039e6103085101dcb0fea2d0fc06d0f7fda0f380c0f314a0e6aa60e1b320e09830dfca40df3090dbd490cc1260ca0890c8b7d0c4abb0c250b0c0cc30bdcb70b71420b517e0b3ae10b3a020af0af0ae7590acf050aceda0aa6f20a2ae70a29560a1e83099a8309955308083307e19f07ca0c07843c077f0c0767a6074cfb070eba06dbc506b3180681a10673ef0647ab0632db05dc3d0550d304f4cd04e4c004b1e104affb03f4cf03eeaa034c7d0310fc0310c902f9f802e16a02c55202c00a029c7f02896e02572602126e01cc1b0183510160ac01609d01548001091701081400e07500cc08004396002a8b
 | 8=>0xfff45affcc48ff9304ff907eff7fb9ff418eff2364ff169afef7d0fe3023fe23e9fd9ed1fc607ffc299bfbff16fba734fba384fb18d5faff5bfafb61faa641fa81ddfa6d14fa497ffa48b7f9ff21f96249f95813f88cb9f87ef8f843b3f837fff77d3bf764adf75bebf73125f726a5f6ff80f63abef6084cf5fe5df5acc4f4ddd5f450aff41188f3c560f392c2f38d48f38c10f35f98f2fe82f24805f1d956f1c02bf142b5f13e4df10492f0b947f096d0f06ae7f00f6aefefb4efa3e7efa297ef6f78eee842eece5eeeba61ee5465ee4787edd9baed9789ed8478ed10e3ec8d44ebc712eafb9eead0dcea91ebea81deea5526ea32a7e96947e9680fe93afce8d35ce85b42e84a0ae80670e7f7aee7cd4be78f1ce6a376e66a1be61896e5fcd4e5e32ce5d828e56fdce44428e41ee2e39012e36d2ae343fae31c18e3157ee27d4fe26641e22d67e1d806e1cacbe13602e0c09ee04a55df192adefd83dea0b7de8852de414ade26c2dd9faadd6b1bdd52dbdd435fdd1e41dcf589dbcc51db8b5edb013ada9498da8d45da1f81d9fbdad9c968d95b27d94f6fd91470d89273d86ed3d85f7ed82b89d8271dd7fee0d7f4f4d7edb2d7b534d7076bd6c65ad636cad63097d629c5d5b8f3d54bb3d4ee6bd4d038d4b89dd41200d346f5d31df4d2a8fad252ded1e8cdd1a2b6d19cffd18274d113a0d0d883d09a65d06110d04fddd03aa4cfcc88cfa35ccfa1efcf6c6ecf6b36cf36bacf32b5ce7f1dce28c0ce07bccdfaf4cdda31cda392cd75bacd639fcce064ccdc60cc8546cc82cccc8194cc77a1cc4fc2cbec88cb9a9ecb3949cb1ef6cb0875caecf4ca5c41ca1261c9e023c9cf85c99ce7c937fec913f8c90095c89becc89b57c8843bc8072ac802d7c802bbc7f7a5c7aea7c7a137c79eb2c78701c77486c76743c73c1bc6f817c6cae0c6750cc60f24c5de30c5ae0cc595b9c57265c55bc6c551bbc52a0fc51a8bc4cd57c4c486c4996bc41ff4c41a7bc3e635c3e620c38801c36e42c3697dc30f6ac29ba0c28361c20663c19444c17999c0e162c084a0c083b0c059eec046bdc03a42c02f9cbfe04fbf9eb6bf7bc8bf5298beef0ebeb06ebde069bdd159bdbb85bdbb41bdab51bd74aabcdff7bc8294bc0e5bbbfdcabbc6dabb7614bb708cbb4e23ba6a19ba6778ba65b1b9dbebb9d9ffb98904b9834db93e59b923d4b91fa3b8c65ab85633b84512b82bd2b80714b7fe31b7b2d6b77dd6b7775bb7666ab74466b63c2ab6331fb5c64cb5af92b595f3b57dbab5234fb51638b4ef62b497f1b462a8b460ccb40d3bb40829b3f5d5b3d58fb3aa61b396e4b38bb2b36586b35498b33863b31eebb2686db23e3fb222d0b17016b129c3b0bcffb0a35bb07bc1b0168fb010b8aff3faafbf90af044baedee9aea8aaae81d2ae7b53ae7221ae4618ae3601ae0b51add63cad7d80ad6eddace667acd07fac8dd0ac6359ac3619aba62aab9347aaa314aa8e92aa6cc6aa45a7aa1a1daa1936aa0771aa057ca9ea18a9511aa8bab5a8a162a89773a88c97a88935a8879aa848e2a84564a7cedba79678a78956a77d88a76b1fa6c253a6bbb9a6abcda69b3ca674eda6155ea552afa4ac07a45c26a3d440a3bff4a37fdfa37ea7a369c7a3417ea315b6a2ea89a2e951a2db90a2ae71a2ac63a28f6ba28bb9a25067a20a57a1e51ea1c0fba033849fed1d9fa5629f86019f73249f0aba9f09829f00399dbc7c9da2ad9d94d19d6d2b9d3cb49d017e9cf8949cc9449cb3429b98dc9b5be09ae8329a88069a69469a4d2199a38498e70098e44198e3a998c27598b78f98a5c5989d8e985e6d97e17197db0597cb89975ed3973755972d8c96eb8796aac8968ec596446796432f95dd1095b2509566de9510b594ff969463e193a204930c8e92facd92b192929b5691e7ec9116bf91127e9110688f79cf8ed95d8ec9ae8ebfa18e7ae98e684c8e4f0a8ded598decad8de5938d8a758d87fb8d86c38d79218d3e4c8cef2a8ccac38c78128be1c48bd4f18bc5798bad868b3e408b13418a463b8a05c489846b896dc988ba3788652188403e882bb488262a8820c58817e28817d987f50887cfce87aaef878a66877dc28761168725cc86d3d886c7248677ed866a728655dd8655b386207b85edab85b9ce8565c18544f584ee748499fb8499ba8438fa841b8a83a85e83a6b183a0cf835a5b83552082d65182cf8f8292e68268fb8246b8823249820b4f81b8088189cf81726d8153cd813f7181228380cd8180cd4880a0d2808b2d80046f7fc1537f47897ebab67eab877ea1987e61387e3fb57da4707da18b7d8ad47d89a57d47127ccbe97cc9d57cbb657c71257c180d7bd1147bb2a57ba6787b37527b2d687af00e7aee447abba67a9bed7a4aa279de9f79994d791dcd78eb2f78e28c788305780ff277f9977793cb779314778cef778cbb76cccb76af0e76549575e34575c354756a6075029e74fc5474a587748d997415567357897355f9733df973322772f75672dda772ad5b7276ef724c167217c3720c2d71fe8871a56a71810a717e97714c6970f34470b24770545770286270191e6fe9c06fc0ce6f378c6ebf146e836a6e6fc26dcba86d80e96d7d156c1f486be7356ba1ce6b9e156b21246b133d6aea0d6a97476a6e066a3e626a012269ce8369a691699ca2695847694fa5691eba68cf1a68b9e7689611686deb686477684d0067b162678b5d677a7a66cf24666ea5664d3866455e66420e662b2365b12a6546776506d064f9af64c817647197645da564041f63bd6463bb5e638e096388c062e31d62b28a628c94625d486231ae61cc8b61c1f661b7ab6127d0611c8260c60c60a4676060e55f99e55f0a035ecc7a5ebc185eb05f5e80535e47895def3e5dcfb85d9aae5d99795d755b5d72a15d64995c969d5c49335c1ec75bb6d55b92315b44af5ae15f5a6fd95a25af597e95596eb2593fff58b9ff589f6257c24956aaf7564edd56421255839f55691054fda754d44754a36d54647654588254094853c4f853ae2a53abb053aa785328c0531547530b7c52ce275289185270df5238d1520f1f51ddb351db3951da0151c507517c4650a66b50a61250a4da50a20a509f855097fc5029794fa43b4f477a4f13f14f0f284eff294e9f7f4e64304e59024dd0574d5dbd4d2a254d24014d23db4d00e74ce6f44ce6f34ca8784c8cd34c7a9f4bf63c4bdf124b96ef4b80164b7cf34b2c9c4aaccb4aaa284a741b4a626d4a1f7b49d59749d35049c48449b722495949480a4647f77d47f40d47d5af47ad84479db947516a46e4dd46cb9a46c93346bc5846bc14469d71468d12465e7c463b594639cf45dd0d45a70b4592af4525f044fe9d44c200445d88441b444376ce433cf343133542dc4541c00841b4bc41a60141a2be419faa417273415b9c412c4a40f9ac40a16c4092884085c3407ea940503a404c533ff89f3ef75f3ea6ba3e8e2c3e7e8d3e7b343df7f83dda3b3dd1d13daf623d6bb83d0ad13cd6623cd6433c7b443c78ca3c77923c214b3ba11c3b7a403b40a43b3f123b3cf73b35cc3ae5623ac2253aaf0d3a70473a15f23915a139066d38f69338e3f33852e437e5e337911a37878a37868f36ae8c368be236692c36156c35f20835aab43548303547b935309934b5d3349004343a4433d995338d48337ac1332728330d8832beb732a92632919e32688e325a6931e6a831e36431598630f56430d760307c68307a9e307772303d86303040300cb42ffcdb2fe55a2fca462fc0572f9c0f2f0a3b2edf9a2e097f2df9cf2defe02dc67e2d8a3f2d57a12ce0ea2c96722c80142bf7e92b9c762aad922aac5a2a978a2a74f82a2fc62997b82968c6291bff2906d228edab28a01928914e287f40283a0627c3fb279e992799912783b62773d42756132743e325fee6257b5f2566eb25658725133e24d521242d4423cfac23ce7423c57723a2b223923f236b12234e4222d92c22d39122c72521c348218a3b21712e211c802104a920dbd820b2fd20addf207e401fe46d1fb6c21f98521f694d1dafe31d83231d05f41cfe681cfc091cda5d1cc0021cb6131c55991c06291baddb1b8cc51b357d1b17ce1adca41ac0e81a7bb019ec3019e9b619e87e19bc4e198e3c18e2ea18de0918c439189760188d711865f81855f8184a4017d180178443177c98173918168fe8168f7616712f16677f163a2c15a89c158c0f14dcde1455d81435b613a80b1386a0135f22130bb412ddfe12d66a12b8a5124875112e911105f310c800108b39100e7110028a0fdad70f76c20f1dec0ef5980ef16b0ece6b0ecab60e8e0d0e60fc0e5d090e484c0e28d50deb8a0dc16e0da12c0d91af0d88ac0d71220d0bd40c9b940c85450c60e10c60ba0c08c80b7e6c0b794a0b69ce0b446e0b00060a235609d01809ae2e099a830973f7088a4108648e086356084764081bf707ea0c07c9b607c67307a3790796bd073a9907189506a54306a25e068ba7065c6b064a250647ab064673060b2e05f93f05d30e05146004e4c004d1e70459df042c1304155c03d0a30384b102f9f802c57402bd8c029621028f3f0277a202126e01d4d301c4d1018af2015b3f00fd4600c3cd008d07002338
 | 9=>0xf95813f88cb9f35f98f142b5f00f6aeecbade9f2dae221afde8852d9c968d94f6fd46451d113a0c89becc51a8bc20275c046bdba6778b77dd6b4ca8fb497f1b17016b0a916afbf90aedee9a41aada01e5997cb89944c248e7ae98de5938d8a758d87fb8d86c38a05c48656ea83a0cf81e6918189cf813f7178830571c22e69a691699ca256e23f5569104cb2b54520b941a601407ea93ea6ba3cd6433ba11c3159862b9c762773d421a99615a89c0ecab60c85450b794a04e4c00277a2018af2
 | 10=>0x788305
 | _=>0
def Pm15419:Nat->Nat
 | 5=>0x50c8d0001b09d0003cc790001bcb500050c4d0003903d0001e4570004e0550004387d0001e43f0004385d0003bc570001e42f00050c750001d0a10001b03d000004240001bc750001e4770004a4a50000b0a1000070550003b89d0003909d0002942b0004fc790003bc2f0002289d
 | 6=>0x7d4e5000ac87d000ac47d000ab07d0012dca50005d0c9000ec8cd0009188a000754cd0009203d0008ec5f000d80750007b03d0008bc570013cc7d0003e4540008a4570006c4d5000490d50000bc3a0000dc3c0007f47b0007f09300077c5a00023852000454c9000f8c770007e8770007b0c30008a87d0008ec4700077cc3000f643d00075cc3000b90750008a43f00119455000744570001742b0007d4cd0011d87d000e34750013404d00048c9d000e149f0011c82d0007e857000474cd0004703d000fac52000e7c2d00016857000f689f0005b0c30008ec370004405d000718570008bc3f00039c9d0011d85d0006489a0015443d000fb02d000d68cd00091475000518c300033075000460a50001683f0002105d001110770002b4cd00049cc30007e83f0004b0570014ac9b000430c3000e142f00040cc3000dac770003c8930007443f0004b02f00102c8a0007183f0005d0dd00078075000348c30002107d0004c8570009f4a10002787d0004b03f0004407d0010a4cd000b3c2d000b3ccd00131c9b0000dc5e0003a87d00129852000268c30002785f00027854000e142d000238930000accd000258570001743b000168770009e477000b9ca5000b90b5000dd045000850a1000848a1001340a5000850990000dc460004c83f00154ccd0004b0770010c4cd000cf82d001540cd000118930002583f000ac8a50014e49d000ac4a5000ab0a5000f8c2f0000dc5f0010143d001110a6001420cd000af0550014202d0006f4d90011102f000d68d5000808770009dca50007d47500001cc30013c8d5000b107d001360cd000b1052001548c30011109f001538c30007849d00091ca5000190730000dc470009bc3d0012dcd50005eca10008c0a50008ec7f0005ec99000f8ca60008a8a500049c6d0008bc77001488c30013cca50008a47700146041000f8c3f000490c90011705d0011103f000cf03a000840a50008e8550009349a000b105d0003d4390015488a0011c8750012507d0007d4b5000b90cd0009e82d0009209d0007e89f000b3cdd00119c9d001198cd00084c3d0011943d000490d9000f8c9f000a2c4d000454d10012f8c300031ccd000e143f0011009d000f5c7200074477000f8c5700071877001298930007d89a0011d8a50010a4dd0014aca5000c58cd0014dc730007543d000334a10011dcc300084c2d0009e43f0012dc7d000fc49d000fb0cd0011bc7700111057000f8c9d0002b455000e1457001250a5001130c3000bc072000128510010cc93000eb8cd000e7c750002783c000faca500102cc3000180a10004c8770007844f001170a50004b09f000e34dd0003302d0011bc5700114871000440a50008083f0010d4a5000f64c30003a8a50013409b0003e47f0015682d000470550003e458000f6c77000f6857000f30c3000d78cd000f189300098c290009a03900082024000e14770006484d0014885d0008082f000c045d000cf875000e449300031c3d00018ccd0011bc3f0002787f0006042d0015405500027858000f6c57000f683f000c68cd00025877000dd0c3000b1435000d4c5a000dac57000e34cd000bf49d00031c75000be0cd000d7cc3000f682f000ac45d0007e82f000b90e50009e42f000ab05d000c047d000a743d000f8c9e0002707d00077c72000b904d0007e827000cc0c3000af03d00039c6e000c98c3000ac8d50000dc7f0010a475000dac3f000f6c3f000f6877000e142e000ac85d000bc8c3000bc0c30009e83d0002705d000b105e0009bccd001198550014a8720001682f0000dc5d000808570009dc7d000b14c3000eb82d00091cd5000908cd0008e83d000adcc30012242b0008accd000dac2f0009e457000b9c7d000b908d000a2cc30008c07d0008a85d00018cdd0000dc450009a8c3
 | 7=>0xdc446000fe0940005c475000950a20003f0b6000c705d00095042000ba8cd00092c2d0007ccc30007c8c3000848cd0003f83c000b607e0003f027000c48b50004589e00079cb200029ccd0004e901000794c30007bc7700022857000c982d0010f455000398be000fa4b60003f040000390870003242b0009805500094cd5000b5075000940d500038836000770c9000398a6000378ae000cc4af000370ae000b40010004f89d000768c300076083000df49f000e147d000f74be0011143900054c2d000374a6000370b600036ccd0006049d000cc8a1000c88a7000f78c9000c84af000334be000fd0a5000dc47f00032427000b2ccd000c707a00071c83000718c3000c70a7000334ae0005c8d50008b8d50006b44a0004d4550005c4550007e0c900002c700010c8450005ac550002882b000fe0740010c0450008acdd000f589d0005c43d00007055000428c90000e4cd000bb1050009749b0004d09e0008309e0006885a0006f0cd0005c0cd0006d0c3000574cd0005c8720002d887000810a6000458ae0002d0a60006b8c300054c5500106cd50005c0750007c8820003f08c0002d8360002a47f000444b6000a4c7e0000c08d0003b07200022499000b045d0007bc57000d009f00041c4700082cd50007e8510007e071000a144d000288be000824d5000374730010a04d000b2c55000678fb000ae07e0008943e000ebc9400104c3500042075000378a7000bc8a1000ebc840003f0be000ae05d0007cc42000b6c9e0010406d000808a5000654c3000bc899000ae9050004dccd0004d505000f24550007f4e5000bfc7500022877000b74af0005b8a2000244ae0010486e000ff87d00022caf0003706c000b4ca7000ff4a5000b44ae0010a0d5000c58c9000fc4350003d8550007a4e5000b5cd100091ccd0002282f0009249d000dc45e000c6c7f0003904f000ebc24000470cd000d002f00036c9d00046ccd000ee8c9000c449f000374be000450d5000a58990009e49d0003d875000dc47d000b20d90001d4d6000ae07a00043055000ae0a7000a2ca50004584e000ff44d000420550005b8c30005b4fb00049c5700040c9d0010c85d000b4078000a14a60010c05d000de067000cc03d000c6c58000d50cd0000803d0005c09d000734a50001d8570001d4770000049e000a147d000f70d5000fd04d000188ae000ab0af000aa0a700058c59000fe0680004505d0006b4a6000f987a000188a6000564c3000fe001000d74c6000a0c75000e309a000e2cca0000089e000ab89d0002d867000154be0003b0d50004209d0006f055000f7437000fd0d50007bc3f000154ae00024d01000668a6000514fb0007c4cd00104c45000378a50008c89e000ba89d0010408d0004302d000288ae0000f8be000f388a0004d0930004ccc30004c8fb000084c90000e0a600034ccd0000dc870000f8ae000ce89f000a10af000b14cd0001d83f0001d4cf0009e4550005c49d0003d89d0003742b00094c7d000c7899000fe030000ac4c900039456000bb499000cc4870000b03600022c36000c4899000ff45d000b4058000c6c7d00091c7d0002409d000ddc350000389b00066873000d002d0009e0af0007c8400004f875000458930009cca700006c7f000f68cd000c8436000efc4d0007a4c9000b6c72000054a60009acaf000c705f0001d8770001d43f000fd05d00041cc3000f8c3a00037c5e00003087000414c3000410fb00002cbe000188400008a8a50004505200001cd60005f0450000542f0000107f000e34d50005e4a50005e0d5000974a7000e5845000da075000a747f00002ca60003e4a2000004c60005d0d5000e78b2000a5c9f0007cc7e000280cd000010470003dcfb0005b8a5000e2445000d6877000188be000f4875000008b6000004a60007949d0006d0cd000c909a0010f8870004b87500024105000838a50010a4cb000dc0d50010f84f0008f4af000398930010e07f000154b6000ddc6d000390c30010f4cd0000b82f000a7458000dc05d00013ccd0010e0370008047d0004d0a60008f0a100037083000e144d0008e8a10009202d0004507d0006509a0000f89e000358c3000b4040000a6c55000b6cbe000bb03d00050cd50007e88d0000f8b6000b407700033493000d4435000088c9000d585d0000549f000b4c5f0006b4720001dccd0001d83d0001d4cd0006b82b000dc8350004d0770004f0d500022801000c08750000082b0004e915000ebc3000075c9e000b402c0002883b00032477000e14d50002646e000458a60009b09d0010089b00045870000f3841000cc49b000830c60002689400104c7f000444a6000ffccd000820360002d8c3000dc8cd00001c56000810ae00104c370000543f000ae05f000ad887000158cd000ad07500080036000779050000086c0002a4c3000ad89a0010048700029cc30003f0a6000bb09d000c9cd5000cc05d000ab087000448a5000aa87f000ff87f00091c55000cdc820007bc32000e585d00002cb600042cd5000284fb000428d5000c707d000274b2000e245d000268c3000ffc55000008ae000108cd0001009d00025cfb0004d058000cd8350006a87500029c55000b2c750001d89f0001d4570005c852000c545d00039036000234fb0010f49d00037057000fa4be000f2475000228c30008949f000ddc8d000b2c9d000370a60003bcd5000dc07d0009309a00033468000768af000760c600075cc60010e04700032457000d5035000cd8cd000ae8cd000334a600059499000080550010d845000f74c6000a106700071cc6000718af000d587d0000549d000f74a600049c3f000e403d000bfc9d0000b8570004449e000918cd000ba86d0006d8360008accd00029c8a000b94450006fcd9000188830007c475000080750006fcc90009ac36000c6c5400104c47000378a60002b451000a0c55000008660009443000015493000ab8750007609e0009505a000980750009747f00018857000ba8550002cce5000668c6000e98cb001004360005b87e0003f0b8000944940005bca50005b47d000ae07d0009303600010cfb000228880007c8370004cc7e0000f893000fe03c0000f4fb00072cc9000c70450003989e0000545700049c770003d8cd0000dcc300022827000c547d0000d4c3000a6c75000b5076001084550002a09d0000f827000270d500061caf000ab84d0008c8c60007f4c900049c9f000ba875000ebc2c00024d1500013c9d0008809e0006e44d0004cc520003243f000090c3000370b8000a0c9d000d749e00052851000074b200006cc3000068fb0005e4a70007c85700088cc6000e20be000880ae0005b87a000a0ccd000f74ae0005b8a7000d64710000f055000e20b60007a4710004bc7d0005d0d90004b8b50004b47d000c442f0001f4d5000030c30007709900002c930004b0a5000de0870007c89f000b0c3d00001ca3000ba84d00072055000dc4ae000010c3000a14a5000b945d000830b60007c866000594a10001546800000482000de03600091875001014cd000ddccd000ebc54000df457001114fb000154a6000dc43c00037040001100fb000538360010149d000d74a6000e44390010f8c30009fc5d000b5cc90004d060000d74b600086c9a000ebc4c0007bc9f000a58390010e0c3000fe06c0007c82f0001d83e0001d4ce0001909b0000202b00041c5d000d002e0000f8a6000d783d0004d0c60000809d00084855000d00d60003349e000b4030000f6c3d000138e5000f683500094401000c889b000ce82f000eb845001080fb00094ca5000104e5000f48cd0010f475000ab86d000a745400010c750007686700095c45000d003f000df43f000d689f000f48d500094c5d000458c6000df42f00065cc9000e9455000264c9000dc4a700002c62000fe064000cc43600088c9e00104cc3000448a700071ca60007987100098441000950460007a0ca000f24d50001d42f00041ca7000c707f000c6cae000da09d00084875000414a7000098d5000b4024000e20ae000b4002000088d50006f075000914aa0007e8710003f8ae000ab85500001037000428d9001004c3000008a6000070750003f09e000c20010000f4a2000dc447000ff8c30004505e0010d85500094470000b9872000de04f0006b4ae000ff4fb000fe093000038a5000c44570010f8360000bcc90000e4350000f8770002f45d0009189d000018d5000fd0c30008d435000d00cf000f749e000fc4fb00051455000398c60001809d00086045000d683f0009b0cd000390af0006fcd5000c705a000e94cd000d74be0007049a000388af000668be0000549e000ebc6c00033460000374c6000370c600065087000e8c5500034829000f98c3000a5851000fe02c000e54cd0008d4cd000cdc570010989a000334c600102076000b7436000b6cc60003242f000cdc6c000d005700079c5500081c7a00001cce000bfccd000f64c3000b4c7f0004f855000b6cb6000b44a6000f249d00061c87000b4027000f60fb000c6ca700025c8d0003709e0005c8a500095c5d0010a4d500010c350007c4350005c4cd000c443f000df43d0000b83f000cdc2f0007ac5d000f38c30008942f000dc4a50002fca100022c9a0006b49e0007cc7a000cc4670002d8af000b145500061c9b0002d0ae0007cc460009b0550005c0550002a4a7000ae07f000c089d000ad8af00063c55001050d50001f8dd0009507e000fd07e000efcfb000a4c72000c7047000c44770001889e000288c6000ad84f0007c8980001d07d000aa8a7000aa07f000dc445000fe070000ab04f00022880000fe058000aa847000ebc93001008a5000aa047000ebc010010145500001c75000b98390006e4a5000d00cd000a74ae0000b87700006835000ff4d5000c6c3c000a5cd60006e45d000ae05a000df477000f7480000a6ccd000944540006b0d5000fe024000c203c00044472000e78fb0000b89f0004d0b6000dc45f0007f855000068cd000b2c3d000a5c77000f74720006d08a000cdc66000e48c3000c98cd000a1087000450a5000b20c9000b1d01000e209300010c8d00094458000e14c300036c55000b6cae00081c39000c6ca5000a1036000520ca00091855000f84d50004d43d000680c90006d49d000b4c470007c45d000420cd000c443d000458b6000188c6000eb855000de0c3000678b20007ac450001549e0007c83f0006fd0d0009e0870009cc7f000444be000f24cd0009e04f0002889e000150cd000880720009ac8700041c5f000bfcd5000d0077000154c60001805500006c7e000d68570005642b0003749e000b0c75000da0550003f0c6000a74a7000ebc68000f2cd5000a5ccf000d50fb000ad86700010c9d00037466001020750005b87d0000f8c600097447000b1475000ebc70000ab067000930af000aa85f00094424000aa05f0000e0ae000288010002289f0000dcaf000c70a2000118a10007c877000da0cd000398ae0007c8ae000b349d0005a8350005a45d00039067000c6c5f0008f4360006e47d000a5c3f0001d49f000cdcc3000374ae000370be0000b0af000ab09b0008c8ae000e147e000cd4fb000ea8d5000ce8770000bcd1000dc45d000ab835000334c00003249f0008c8a60003349400006ca7000e98d500015055000ab8cd000334b6000b4074000e20a6000b0c550009b0750002e471000f6875000d60c9000088d9000aeccd00088cae000084d10009e8c9000880c60005105d00049c2700020c55000264710002449e000c70c3000038a7000314c9000030af00002cc6000c64c3000880a60006689e00001cfe000f689d00006855000010a7000f489d0008109e0004b0d5000cdc3f000008c6000b403c000004ae0010807d000830be000ffc9d000b0c9d0004bc39000e24750009e067000d74ae000830a6000810c60003409a0010f8af0002a45f000de4a5000abccd000ad09d000dccd5000810b6000c0855000a80cd000a74a500047445000288b60010e0a7000abc75000f6855000a5ccd00103045000a58d5000ffc75000fa49e00010c5500042ca50007bc2f000228780005ec3a0009745f0010d03100045862000d58d50007c827000b98c3000b94fb000ff87e000df43e000ffc4d000ce857000244a6000ae0a2000ff4a6000ff85d000228c400013c55000c08cd0008943f00022c87000c2024000dc4a6000ff47d0005a845000cdc27000c6c5d0001049d000b4cc3000d1cd500005477000cdc98000cdc4a0007c49d000d10d5000c70420007688700036c750008c827000760ae00075cbe0008f099000b4057000008730009f49d00104ca70009844f0008c8be0008489d0003583d0009d855000e8c9d00075cae000af4fb0002b47100071cae0007188700089457000cf8560003e035001048a10009d82d0005107d00101036000cbcd5000a5c2f000f84a5000f149d000e209e000cdc9f00091c75000ae0c3001008a7001004af00088ca600037c5d0003f077000880be000a5c570000a899000c88a50002283f000d00ce000ff8a7000ad0cd000c78c900065472000ab8fb001000d1000c78e5000c70a5000aa0c3000a4c5a000abc9d0006b4c600012451000c48c90003e0cd000830ae00092c55000a58c90002cc9d0006b4b6000920cd000980cd000918d50003045d00028475000810be00092455000b149d000358350004745d000fa4c60001509d000204cd000190a5000b607a000a4cc3000b40540002dc45001000c9000f4855000c6ca6000650af000c202c000668ae0008b0cd000b0ccd000b6ca600042c7d0000dc36000c443e000b403f0002b44d000ce83f00065036000358cd000b4c37000080cd000a14fb0008943d0007943d000a10c30005e49b0005e0cb000eb87d00028445000a6c9d00002c4e00085ccd000eac7d0003d835000f14550002646d00091c9d000cdc770009508c000ea4390001d82f0009e0c3000768360009446c000760a600075cb60009ccc30009c8c3000e787d00025caa000fc4cd0010c839000ad836000b30a5000bfc550009acc30005b87f0000303600002cae00071836000b20d5000b1d1500001cf600037c7d0000105f000ab036000008be000aa8370011147a000004be000aa0370008c857000fd07d0010a09a000ee8d1000e40cd0004cc72000ae0a5000950c3000228350009809d000ad035000944930010f8670006b854000ad05500010ccd00089477000c849b0006b4be0003047d000914fb000dac5d0004d054000784cd000cf8750010e05f000abc550004d048000da0350008f8c300013c750004d02f0004fc360010409d000a587100077c750002dc5d0004d0be0007589d000668b60004f8cd000d508d0002bc450009503e0007c4550002b46d000b402f000650670004d0ae000e20c6000ebc58000a50d5000374860001904d0006b4370002682b0004489b00015075000864c30006f4550005d0c9000138c9000de0af0010dc41000cfc7d0009e0360002648d00061c36000cf47d000458be00104c5f000a0c4d000a74a60009442c000a5cce00083093000444c6000190d50006f03d00081cc300101475000e98530008108200041c7f000444ae0004203d0000c06d0004147f001004670009eca50009e8dd0006f09d00003c520003f8a600028455000c94a50003f0ae00006c7d00097437000ff85f0005646c000c707e
 | 8=>0x2ce6000010ca0000f4a60000a4350000504e0000bcdf00001077000070d60000e4d60000d852000058aa0000a8550000f07c00009c520000f49b00007878000044e600004829000084ce000094ca0000f0c80000909a0000649e000064d6000078ca000060a60000b8fe00005ca400005c2c0000705600000c0100008c9a000028f60000289f00009c3a0000789f0000e0f60000b83a0000ac01000054ab000050fb000028de00007c580000c43a000040d60000b0fe0000acde0000dcb60000dc3400005c600000e8ca0000fc350000f852000024f600005c9e0000707200000c560000f09c00003cee0000a8df00005c70000024d60000a4de0000f4ce000020a80000f8820000d8870000a0c600007ca40000d45500009cdf0000207f0000bc3d0000a89e0000305400003047000028ce0000506600002cee0000f0c00000149e0000f0350000d0f60000d06c0000902e0000283f0000383a000024570000203c0000647600001cfe00004c36000078760000883a0000ccf600001cd600007835000024770000b84e0000643a000048760000c82400002c3700004cc300008cce000098fe0000ecca0000f0900000789d000090ca000048fb0000089c0000703a000028e6000094fe000020740000283a00005c01000048530000082c0000c84c0000647c00003c010000f83e0000fccf0000cc2a000018de0000f4010000087400002401000024ee0000c4870000309400005ca80000389a00005cc4000044c30000a8cf000028cf0000d4cf000054720000a49e0000482b0000489a0000146000002c760000c0de000090d60000d4770000b84c0000a89f000028010000bc87000014c60000f045000044ca0000f0a000008cfe000014ae000010de0000645e0000145c0000c83800000cf6000040aa00005c0a0000308c00001cee0000acb40000b8520000c0ca00000cd600002c9400004cd60000b8f60000b86c0000e85200003058000028940000483700003cc30000f04000004c760000283e000088df00002c4a000084de00006077000080de00007ca7000078fe000088ca00004cca0000f8550000044800000c5200002857000008a60000d8c00000c076000058ca0000e4ce0000b0de0000acf6000030c300002472000048d500005c07000004be0000fc3d0000f05400002cc30000849e0000eca6000000af000014340000082f0000acce0000483e0000d4ce0000a877000030a0000004ae0000a887000084560000305c0000a4d600000444000044de0000288c000070fe0000d49f00005cb000000c760000a0b6000020940000cc9d00006c010000b89a0000b49a0000d03e00006480000028ca0000d0ce00006cdf0000303c0000283600004c520000ccce000068de000064fe0000103e0000f83f00005cac000060c600004cce00007c02000024940000fcaf00000cca00007c540000f8f60000f0b800006470000014b6000028c30000fc3600003c820000f8e600003c900000849f0000089f0000a09e000010d60000f8cd0000043400000cde00005c5800003cd6000064720000fc9d0000e4ca0000f4de0000f0a800008801000098de000044360000b8a60000742b000080ca0000e0ce000024c30000f4d600005cc6000048ce0000f07f0000009d00003cca0000ecde000034400000243f0000f0370000083f000094ee0000783e0000e8fe00005c740000309800002cd6000078720000249a00003078000020c300006c3f0000843e000020010000bc570000a02c0000c09e0000e8e60000403a000034a500001c5200005c9c00001058000058de0000a43e0000205c0000e4f60000bc770000085400005c03000064ce00005cb80000c4ca000054ce0000749b00001c3a0000e4e60000745300001caa0000049e0000c8280000287600007c9c000090f60000342c0000d43f000028880000f86c000094760000f03c0000b8ce0000fc770000943e00000c66000028d6000084760000ec9a00009c7200008cf600004856000054fe000050df00006c3d0000c89e0000f89d0000fc670000e0fe0000305e0000bc9e000064010000f8de00002482000048390000d0ca0000849d0000089d000030b400007c300000c03a0000dcbe0000f0640000bc3500000c9a00007c80000078f80000ac9e0000202c0000b45800007cc4000078c40000dca6000018ca0000cc52000080f6000078ee0000f4ee000018ab0000e88c000014500000f0470000d8af0000a8cd0000bc9f000034a40000487d0000744c000020980000e8ee000030a40000f02c000028370000a89d0000042c000048c90000d89a000048710000f074000070ee0000ec720000d0de0000f0b00000b43000007473000010ab0000b89e0000e4ee000008570000d0e600007c7c000054a60000903e00009cca00000cc30000080200004c320000ccd60000f86600007cc800007852000064ee000060be0000604c00004cfe0000f8940000cce600000057000098ce000048d70000ec0100007438000078ce0000fc550000349c00001c860000f4730000e0d600003cce0000e89a00000493000020580000c8be00005cc00000f0940000a87500006c57000000fb00005c9400005c7c00005cb600005c340000dcae000030020000c8ae00001001000010760000b49c0000003d00000077000044fe0000c4af000088de0000603800005c0d00007c01000030480000d86700002c3e000020a40000643e0000c0f60000489900002c720000e0350000b4a000001c9a00008001000014a60000d08c000008a00000f0360000f8ce000058d60000305d0000bcaf00000c800000c0d600001856000000cd0000fcfb000050b40000f08c0000f8c3000030440000083c0000f050000040de0000483b0000180100005cbc0000b0ca0000d0ee0000783700006c5500002476000008010000b0720000a8010000f8ca0000707600005c280000c8340000d8ca00005c090000f4990000f8770000e09e00003cfe0000b8de0000ccee0000f4ab000034020000b8e6000054f60000508700006c350000b4010000f0c3000034a70000549900002cca0000bc010000249d0000b89b000044760000ecab0000443a000030a70000b8010000704e000004a60000e8aa0000243e0000b0f60000acfe00002cfe0000f05c000048cb00004873000030700000ace60000a04800000000000010ce000050ca0000a8af0000d4cd0000644e0000c8b60000a4fe0000ac750000e4c30000a0be0000a84f0000d47500009caf000030bc000034580000b8530000b47800003030000090ce00002880000030600000dc400000a044000064900000f046000024cd0000f034000070ca0000089e0000609e000014720000dc380000f8d60000c0ee00003430000028fe0000e83a0000f8980000f84a0000583a0000bc360000c4720000e0aa0000d4010000d8bc0000b88c0000a83f0000f08800004cee0000bc550000909e0000107500002c350000dc93000024fe0000487f000098f60000709e00003c4e00005c6800005ca00000b8ee000034010000e0ca0000f0980000f837000044320000306c000018750000bc750000ac8c0000e8d60000bccf00003c52000020a70000482e00002878000094f60000d8fb000084da00001c660000489b00002cce00002c01000094e60000d49d00007c7400000c3a0000b0d60000b8b80000acee0000889a0000e4de0000504d00002c9d0000a4ce0000489e0000b43c000044ee00001c72000030740000d0ab00001cde0000a867000020bc0000e8860000a83500007c780000a0ae00000cce00002872000090fe00002060000028750000209c0000cca3000020780000e42e00003c660000fccd000090e60000b8660000c8500000f8010000f0b400008cde000040f6000064ca000088cb0000809e000044ce00008cd60000bc9d00003cde0000543a0000f87200007ca800005c0e0000c893000084ca000018fe000008780000f4ca000084d600002437000080fe00007c7f000078f60000746000006ccf000098d6000030800000f03800000840000030c40000f0a4000080d60000305f000078d60000d09a0000c4fb0000f00100002cde00002c6c0000904c0000843f0000f876000048a50000643b000050720000d457000094d600009c9a0000189a0000c0c3000048450000409a0000b870000050650000d0d60000745c00004c9a0000d435000038ca0000bcfb00005401000070f60000f8570000589a0000d43d000010fe000094ce0000003500006460000070e600000cfe0000606000007ca00000d83a0000ccde00006c360000ecce0000fc3f000068d600006ccd0000307c0000dc9e000064f600008872000028f80000b4540000e4760000b8ab000090ee000028c40000643900002466000028ee0000b402000030c8000064de0000309c000060ae000080ce000084cf0000d8860000605c000054ca000088c900008cee00000c74000074340000f0020000000100005c40000088520000b440000004c60000c8a60000b0c30000acaa000024de00005852000000df00005cc80000f83d0000009f0000083000006c9f00005cbe0000289d00008457000098ca00003c9a0000f0480000a8fb000024ce000020800000a4aa000020c400005ca6000080ee0000205f000078de0000a09300005c3c0000f8cf00009cfb000034a60000843d0000f89a0000b8990000f0680000fc9f00000cae000060340000c4520000f0440000485d0000b83c0000fcdf000058fe0000f4720000f8fe0000ccca00001cf60000a85700000858000030c00000a0300000d0e80000bc3f000070de000024550000ec520000a83d0000043000006c9d0000e8720000449a0000b8d600000877000024750000b8510000207c0000e8660000f4fe0000f43a0000505200005c240000289a000020c8000098c3000064e6000040ca0000f0a7000060b60000c49a0000283d0000249f000054de000050af000084cd0000ecfe0000645200002440000030900000504f0000e8de0000f0700000acd600003c760000c072000094c30000300100005c44000018d60000789400008c40000024ca0000a8360000fc750000f0bc00008455000034740000e4fe00008cca0000f89f0000a0a60000d8720000f0300000f0600000dc3c0000f8ae00005cae0000b42c00003c3a0000285200002c9f00006456000024cf000028350000503a000090a2000014be0000144c0000e056000018ce0000109a0000d8850000f0780000509a000030400000385200008477000010f600000cf80000e0de0000ec9900000cc4000020c000008cab00000cee00007c400000bccd000028cd0000d040000020540000dcc600004cf60000fc01000074500000f06c000024980000508c0000b09e0000f49e0000b8e8000048a700004cde0000f486000008a80000cc3a00001cca000080aa00007cc3000078c30000484700003cae0000acca000094de0000d8df000054d6000050670000b0760000b4740000d4360000143800006801000004b60000cc72000000360000645300002877000074c30000f47100005c6c0000648c0000003f0000f88c0000605000006c770000fc570000d0fe000020a00000743b000044f6000070c30000285500007c3c000044d60000a4ca000090de0000ccfe000008a4000034780000b8ca000034a0000000cf0000e84e00008c3e00005c0b00007801000098760000fc87000084370000302c000064c3000034540000cca10000f8ee00006451000020400000f0840000742300005c6400007c2c00008475000000550000043800005c3800008401000040fe0000b0860000f49a0000f0580000fc9e0000349b000030b800006c750000f4f6000078800000b07e000068ca0000387200003cf60000343c0000b0520000c8c60000f0800000009e0000f0c4000034a80000549a000040520000f0ac0000f05f0000f04c0000187600003ce600004ce60000ecd600005c93000030a80000485f000020300000c4df0000e8f6000024ae0000307f00004835000000750000243d0000b03a00005c05000088dd00000c8200002cf600005cb4000048510000c0fe0000f8750000805500002002
 | 9=>0xa40000002c000000600000009e0000007000000078000000080000008400000001000000a8000000c4000000540000000a00000007000000b000000048000000ac00000058000000c600000050000000740000009c0000008c00000003000000b80000004c000000060000000c0000005c000000c0000000940000007c000000b6000000340000000d00000030000000bc000000980000002800000009000000000000009000000068000000a0000000020000000e000000040000008800000040000000c8000000be000000a60000003c0000002400000044000000ae000000800000006c0000000b00000064000000380000009300000005000000b4
 | 10=>0x0
 | _=>0
def tgm15419:Fin 7->Nat:=fun _=>0
def sam15419:=0x9f0cf920f137abf9758df66545740435
def atm15419:=0xffffffffffffffffffffffffffffffff
abbrev bfm15419:=bar cm15419 (findAut1 cm15419.shTT sam15419 (Rgen atm15419 10 xtm15419 Pm15419) Nm15419 Lm15419 Hm15419) (Rgen cm15419.all1v 10 xm15419 Pm15419)
lemma bm15419_5_0:span (bfm15419 5) 28 0=true:=by decide +kernel
lemma bm15419_6_0:span (bfm15419 6) 80 0=true:=by decide +kernel
lemma bm15419_6_1:span (bfm15419 6) 80 80=true:=by decide +kernel
lemma bm15419_6_2:span (bfm15419 6) 80 160=true:=by decide +kernel
lemma bm15419_6_3:span (bfm15419 6) 80 240=true:=by decide +kernel
lemma bm15419_6_4:span (bfm15419 6) 24 320=true:=by decide +kernel
lemma bm15419_7_0:span (bfm15419 7) 80 0=true:=by decide +kernel
lemma bm15419_7_1:span (bfm15419 7) 80 80=true:=by decide +kernel
lemma bm15419_7_2:span (bfm15419 7) 80 160=true:=by decide +kernel
lemma bm15419_7_3:span (bfm15419 7) 80 240=true:=by decide +kernel
lemma bm15419_7_4:span (bfm15419 7) 80 320=true:=by decide +kernel
lemma bm15419_7_5:span (bfm15419 7) 80 400=true:=by decide +kernel
lemma bm15419_7_6:span (bfm15419 7) 80 480=true:=by decide +kernel
lemma bm15419_7_7:span (bfm15419 7) 80 560=true:=by decide +kernel
lemma bm15419_7_8:span (bfm15419 7) 80 640=true:=by decide +kernel
lemma bm15419_7_9:span (bfm15419 7) 80 720=true:=by decide +kernel
lemma bm15419_7_10:span (bfm15419 7) 80 800=true:=by decide +kernel
lemma bm15419_7_11:span (bfm15419 7) 80 880=true:=by decide +kernel
lemma bm15419_7_12:span (bfm15419 7) 80 960=true:=by decide +kernel
lemma bm15419_7_13:span (bfm15419 7) 80 1040=true:=by decide +kernel
lemma bm15419_7_14:span (bfm15419 7) 80 1120=true:=by decide +kernel
lemma bm15419_7_15:span (bfm15419 7) 80 1200=true:=by decide +kernel
lemma bm15419_7_16:span (bfm15419 7) 80 1280=true:=by decide +kernel
lemma bm15419_7_17:span (bfm15419 7) 21 1360=true:=by decide +kernel
lemma bm15419_8_0:span (bfm15419 8) 80 0=true:=by decide +kernel
lemma bm15419_8_1:span (bfm15419 8) 80 80=true:=by decide +kernel
lemma bm15419_8_2:span (bfm15419 8) 80 160=true:=by decide +kernel
lemma bm15419_8_3:span (bfm15419 8) 80 240=true:=by decide +kernel
lemma bm15419_8_4:span (bfm15419 8) 80 320=true:=by decide +kernel
lemma bm15419_8_5:span (bfm15419 8) 80 400=true:=by decide +kernel
lemma bm15419_8_6:span (bfm15419 8) 80 480=true:=by decide +kernel
lemma bm15419_8_7:span (bfm15419 8) 80 560=true:=by decide +kernel
lemma bm15419_8_8:span (bfm15419 8) 80 640=true:=by decide +kernel
lemma bm15419_8_9:span (bfm15419 8) 80 720=true:=by decide +kernel
lemma bm15419_8_10:span (bfm15419 8) 80 800=true:=by decide +kernel
lemma bm15419_8_11:span (bfm15419 8) 80 880=true:=by decide +kernel
lemma bm15419_8_12:span (bfm15419 8) 80 960=true:=by decide +kernel
lemma bm15419_8_13:span (bfm15419 8) 58 1040=true:=by decide +kernel
lemma bm15419_9_0:span (bfm15419 9) 64 0=true:=by decide +kernel
lemma bm15419_10_0:span (bfm15419 10) 1 0=true:=by decide +kernel
lemma hbm15419:∀ s ≤ 10,∀ i < Nm15419 s,bfm15419 s i=true:=by
 intro s hs
 interval_cases s
 · intro i hi; simp [Nm15419] at hi
 · intro i hi; simp [Nm15419] at hi
 · intro i hi; simp [Nm15419] at hi
 · intro i hi; simp [Nm15419] at hi
 · intro i hi; simp [Nm15419] at hi
 · intro i hi
   have hi' : i < 28 := hi
   exact span_sound (bfm15419 5) 28 0 bm15419_5_0 i (by omega) (by omega)
 · intro i hi
   have hi' : i < 344 := hi
   by_cases h0 : i < 80
   · exact span_sound (bfm15419 6) 80 0 bm15419_6_0 i (by omega) (by omega)
   by_cases h1 : i < 160
   · exact span_sound (bfm15419 6) 80 80 bm15419_6_1 i (by omega) (by omega)
   by_cases h2 : i < 240
   · exact span_sound (bfm15419 6) 80 160 bm15419_6_2 i (by omega) (by omega)
   by_cases h3 : i < 320
   · exact span_sound (bfm15419 6) 80 240 bm15419_6_3 i (by omega) (by omega)
   exact span_sound (bfm15419 6) 24 320 bm15419_6_4 i (by omega) (by omega)
 · intro i hi
   have hi' : i < 1381 := hi
   by_cases h0 : i < 80
   · exact span_sound (bfm15419 7) 80 0 bm15419_7_0 i (by omega) (by omega)
   by_cases h1 : i < 160
   · exact span_sound (bfm15419 7) 80 80 bm15419_7_1 i (by omega) (by omega)
   by_cases h2 : i < 240
   · exact span_sound (bfm15419 7) 80 160 bm15419_7_2 i (by omega) (by omega)
   by_cases h3 : i < 320
   · exact span_sound (bfm15419 7) 80 240 bm15419_7_3 i (by omega) (by omega)
   by_cases h4 : i < 400
   · exact span_sound (bfm15419 7) 80 320 bm15419_7_4 i (by omega) (by omega)
   by_cases h5 : i < 480
   · exact span_sound (bfm15419 7) 80 400 bm15419_7_5 i (by omega) (by omega)
   by_cases h6 : i < 560
   · exact span_sound (bfm15419 7) 80 480 bm15419_7_6 i (by omega) (by omega)
   by_cases h7 : i < 640
   · exact span_sound (bfm15419 7) 80 560 bm15419_7_7 i (by omega) (by omega)
   by_cases h8 : i < 720
   · exact span_sound (bfm15419 7) 80 640 bm15419_7_8 i (by omega) (by omega)
   by_cases h9 : i < 800
   · exact span_sound (bfm15419 7) 80 720 bm15419_7_9 i (by omega) (by omega)
   by_cases h10 : i < 880
   · exact span_sound (bfm15419 7) 80 800 bm15419_7_10 i (by omega) (by omega)
   by_cases h11 : i < 960
   · exact span_sound (bfm15419 7) 80 880 bm15419_7_11 i (by omega) (by omega)
   by_cases h12 : i < 1040
   · exact span_sound (bfm15419 7) 80 960 bm15419_7_12 i (by omega) (by omega)
   by_cases h13 : i < 1120
   · exact span_sound (bfm15419 7) 80 1040 bm15419_7_13 i (by omega) (by omega)
   by_cases h14 : i < 1200
   · exact span_sound (bfm15419 7) 80 1120 bm15419_7_14 i (by omega) (by omega)
   by_cases h15 : i < 1280
   · exact span_sound (bfm15419 7) 80 1200 bm15419_7_15 i (by omega) (by omega)
   by_cases h16 : i < 1360
   · exact span_sound (bfm15419 7) 80 1280 bm15419_7_16 i (by omega) (by omega)
   exact span_sound (bfm15419 7) 21 1360 bm15419_7_17 i (by omega) (by omega)
 · intro i hi
   have hi' : i < 1098 := hi
   by_cases h0 : i < 80
   · exact span_sound (bfm15419 8) 80 0 bm15419_8_0 i (by omega) (by omega)
   by_cases h1 : i < 160
   · exact span_sound (bfm15419 8) 80 80 bm15419_8_1 i (by omega) (by omega)
   by_cases h2 : i < 240
   · exact span_sound (bfm15419 8) 80 160 bm15419_8_2 i (by omega) (by omega)
   by_cases h3 : i < 320
   · exact span_sound (bfm15419 8) 80 240 bm15419_8_3 i (by omega) (by omega)
   by_cases h4 : i < 400
   · exact span_sound (bfm15419 8) 80 320 bm15419_8_4 i (by omega) (by omega)
   by_cases h5 : i < 480
   · exact span_sound (bfm15419 8) 80 400 bm15419_8_5 i (by omega) (by omega)
   by_cases h6 : i < 560
   · exact span_sound (bfm15419 8) 80 480 bm15419_8_6 i (by omega) (by omega)
   by_cases h7 : i < 640
   · exact span_sound (bfm15419 8) 80 560 bm15419_8_7 i (by omega) (by omega)
   by_cases h8 : i < 720
   · exact span_sound (bfm15419 8) 80 640 bm15419_8_8 i (by omega) (by omega)
   by_cases h9 : i < 800
   · exact span_sound (bfm15419 8) 80 720 bm15419_8_9 i (by omega) (by omega)
   by_cases h10 : i < 880
   · exact span_sound (bfm15419 8) 80 800 bm15419_8_10 i (by omega) (by omega)
   by_cases h11 : i < 960
   · exact span_sound (bfm15419 8) 80 880 bm15419_8_11 i (by omega) (by omega)
   by_cases h12 : i < 1040
   · exact span_sound (bfm15419 8) 80 960 bm15419_8_12 i (by omega) (by omega)
   exact span_sound (bfm15419 8) 58 1040 bm15419_8_13 i (by omega) (by omega)
 · intro i hi
   have hi' : i < 64 := hi
   exact span_sound (bfm15419 9) 64 0 bm15419_9_0 i (by omega) (by omega)
 · intro i hi
   have hi' : i < 1 := hi
   exact span_sound (bfm15419 10) 1 0 bm15419_10_0 i (by omega) (by omega)
lemma lbm15419:∀ t,HasCircuitSize 7 fm15419 t->11<=t:=prove_base1 fm15419 rm15419 sam15419 cm15419 tgm15419 xm15419 xtm15419 Nm15419 Lm15419 Hm15419 Pm15419 rfl (by decide +kernel) (by decide +kernel) hbm15419 (fun _=>Or.inl rfl)
namespace AddInput

-- Adding a seventh input that is AND-ed with the output: a circuit on six inputs with s gates
-- gives one on seven inputs with s + 1 gates.  Wire i < 6 keeps its number, wire i >= 6 moves up.
def sh (i : ℕ) : ℕ := if i < 6 then i else i + 1
def shG (g : Gate) : Gate := ⟨g.op, g.inputs.map sh⟩
def st (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def ins (b : Bool) (w : List Bool) : List Bool := w.take 6 ++ b :: w.drop 6

theorem ins_getD (b : Bool) (w : List Bool) (hw : 6 ≤ w.length) (i : ℕ) :
    (ins b w).getD (sh i) false = w.getD i false := by
  unfold ins sh
  by_cases h : i < 6
  · simp only [h, ite_true]
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, h]
  · simp only [h, ite_false]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have h6 : (List.take 6 w).length = 6 := by simp; omega
    rw [h6]
    have : i + 1 - 6 = (i - 6) + 1 := by omega
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega

theorem st_ins (b : Bool) (w : List Bool) (hw : 6 ≤ w.length) (g : Gate) :
    st (ins b w) (shG g) = ins b (st w g) := by
  have hv : ((shG g).inputs.map fun i => (ins b w).getD i false) = (g.inputs.map fun i => w.getD i false) := by
    simp only [shG, List.map_map]
    apply List.map_congr_left
    intro i _
    exact ins_getD b w hw i
  unfold st
  rw [hv]
  show ins b w ++ _ = ins b (w ++ _)
  unfold ins
  rw [List.take_append_of_le_length hw, List.drop_append_of_le_length hw]
  simp [shG]

theorem fold_ins (b : Bool) : ∀ (gs : List Gate) (w : List Bool), 6 ≤ w.length →
    (gs.map shG).foldl st (ins b w) = ins b (gs.foldl st w) := by
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hw
    simp only [List.map_cons, List.foldl_cons]
    rw [st_ins b w hw g]
    exact ih (st w g) (by simp [st]; omega)

theorem st_last (w : List Bool) (g : Gate) :
    (st w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [st]

theorem fold_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl st w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, List.length_cons]; rw [ih]; simp [st]; omega

theorem lift (f : (Fin 6 → Bool) → Bool) (s : ℕ) (h : HasCircuitSize 6 f s) :
    HasCircuitSize 7 (fun x : Fin 7 → Bool => f (fun i => x i.castSucc) && x (Fin.last 6)) (s + 1) := by
  obtain ⟨C, hC, hs, hev⟩ := h
  refine ⟨⟨C.gates.map shG ++ [⟨GateOp.and, [sh C.output, 6]⟩], 7 + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | rfl
    · have h0 := hC g0 hg0
      simpa [shG] using h0
    · simp
  · show (C.gates.map shG ++ [_]).length ≤ s + 1
    have : C.gates.length ≤ s := hs
    simp; omega
  · intro x
    have hx : List.ofFn x = ins (x (Fin.last 6)) (List.ofFn fun i : Fin 6 => x i.castSucc) := by
      rw [List.ofFn_succ']
      simp [ins, List.concat_eq_append]
    have hw0 : 6 ≤ (List.ofFn fun i : Fin 6 => x i.castSucc).length := by simp
    set w0 := List.ofFn fun i : Fin 6 => x i.castSucc with hw0def
    set b := x (Fin.last 6)
    have hW : (C.gates.foldl st w0) = C.wires w0 := rfl
    have hlen : (C.gates.foldl st w0).length = 6 + C.gates.length := by rw [fold_len]; simp [hw0def]
    have hWlen : 6 ≤ (C.gates.foldl st w0).length := by omega
    show ((C.gates.map shG ++ [(⟨GateOp.and, [sh C.output, 6]⟩ : Gate)]).foldl st (List.ofFn x)).getD (7 + C.gates.length) false = _
    rw [hx, List.foldl_append, fold_ins b C.gates w0 hw0]
    simp only [List.foldl_cons, List.foldl_nil]
    have hI : (ins b (C.gates.foldl st w0)).length = 7 + C.gates.length := by
      simp only [ins, List.length_append, List.length_take, List.length_cons, List.length_drop]
      omega
    have h1 := ins_getD b (C.gates.foldl st w0) hWlen C.output
    have h2 : (ins b (C.gates.foldl st w0)).getD 6 false = b := by
      have ht : (List.take 6 (C.gates.foldl st w0)).length = 6 := by
        simp only [List.length_take]; omega
      unfold ins
      rw [List.getD_append_right _ _ _ _ (by omega), ht]
      rfl
    have he := hev (fun i => x i.castSucc)
    change (C.wires w0).getD C.output false = _ at he
    rw [← hW] at he
    rw [← hI, st_last]
    simp only [List.map_cons, List.map_nil, h1, h2, he]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
    rfl

end AddInput
def rowFn6 (x : Fin 6 → Bool) : Bool := Nat.testBit (3939035272 * 2 ^ 32 + 3938975744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rowBridge7 : ∀ x : Fin 7 → Bool, (rowFn6 (fun i => x i.castSucc) && x (Fin.last 6)) = fm15419 x := by
  decide +kernel
def rowCirc6 : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 12]⟩], 15⟩
theorem rowCirc6_mono : PEqualNP.MetaComplexity.Monotone2 rowCirc6 := by
  intro g hg
  simp only [rowCirc6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rowCirc6_eval : ∀ x : Fin 6 → Bool, rowCirc6.eval (List.ofFn x) = rowFn6 x := by
  decide +kernel
end PEqualNP.Outside.L_meta_15419_aux
theorem PEqualNP.Outside.L_meta_15419 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939035272 * 2 ^ 32 + 3938975744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939035272 * 2 ^ 32 + 3938975744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨D, d1, d2, d3⟩ := PEqualNP.Outside.L_meta_15419_aux.AddInput.lift _ s h
  have hb := PEqualNP.Outside.L_meta_15419_aux.lbm15419 (s + 1) ⟨D, d1, d2, fun x => (d3 x).trans (PEqualNP.Outside.L_meta_15419_aux.rowBridge7 x)⟩
  have hw : PEqualNP.Outside.L_meta_15419_aux.rowCirc6.gates.length = 10 := rfl
  exact ⟨PEqualNP.Outside.L_meta_15419_aux.rowCirc6, PEqualNP.Outside.L_meta_15419_aux.rowCirc6_mono, by change PEqualNP.Outside.L_meta_15419_aux.rowCirc6.gates.length ≤ s; omega, PEqualNP.Outside.L_meta_15419_aux.rowCirc6_eval⟩
