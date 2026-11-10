/- The property of taking one element from Γ and calculating the remainder without x. -/
class inductive Extract {α : Type} (x : α) : List α → outParam (List α) → Type where
| head {xs : List α} : Extract x (x :: xs) xs
| there {y : α} {xs ys : List α} (h : Extract x xs ys) : Extract x (y :: xs) (y :: ys)

instance instExtractHead {α : Type} {x : α} {xs : List α} :
  Extract x (x :: xs) xs := Extract.head

instance instExtractThere {α : Type} {x y : α} {xs ys : List α} [Extract x xs ys] :
  Extract x (y :: xs) (y :: ys) := Extract.there inferInstance

def extract {α : Type} (x : α) (Γ : List α) {Γ' : List α} [Extract x Γ Γ'] : List α := Γ'

def extract_cons {α : Type} (x : α) (Γ : List α) {Γ' : List α} [Extract x Γ Γ'] : List α := x :: Γ'

#eval extract 3 [1, 2, 3, 4]
-- >> [1, 2, 4]

#eval extract_cons 3 [1, 2, 3, 4]
-- >> [3, 1, 2, 4]

/- The property of taking a subList from Γ and calculating the remainder. -/
class inductive ExtractList {α : Type} : List α → List α → outParam (List α) → Type where
| nil {Γ : List α} : ExtractList [] Γ Γ
| cons {x : α} {xs Γ Γ' Γ'' : List α} [ext : Extract x Γ Γ'] (h : ExtractList xs Γ' Γ'') :
    ExtractList (x :: xs) Γ Γ''

instance instExtractListNil {α : Type} {Γ : List α} :
  ExtractList [] Γ Γ := ExtractList.nil

instance instExtractListCons {α : Type} {x : α} {xs Γ Γ' Γ'' : List α}
    [ext : Extract x Γ Γ'] [extl : ExtractList xs Γ' Γ''] :
  ExtractList (x :: xs) Γ Γ'' := ExtractList.cons inferInstance

def extract_list {α : Type} (Γ₁ Γ : List α) {Γ₂ : List α} [ExtractList Γ₁ Γ Γ₂] : List α := Γ₂

#eval extract_list [2, 4] [1, 2, 3, 4]
-- >> [1, 3]

/-- 2つの文脈 L と R を合体させた文脈とその ExtractList -/
def extractList_append {α : Type} : (L R : List α) → Σ Γ, ExtractList L Γ R
| [], R => ⟨R, ExtractList.nil⟩
| x :: xs, R =>
  let ⟨Γ', h⟩ := extractList_append xs R
  ⟨x :: Γ', ExtractList.cons h⟩

abbrev PermList {α : Type} (Γ₁ Γ₂ : List α) : Type := ExtractList Γ₁ Γ₂ []

example : PermList [1, 2, 3, 4] [2, 1, 3, 4] := inferInstance
example : PermList [1, 2, 3, 4] [3, 4, 1, 2] := inferInstance

/-- PermList の対称律: A と B が並べ替えなら、B と A も並べ替え（同値関係） -/
abbrev PermList.symm {α : Type} {Γ₁ Γ₂ : List α} (h : PermList Γ₁ Γ₂) : PermList Γ₂ Γ₁ := by
  sorry

/-- 逆向きの構成 -/
instance instExtractListSingletonFromExtract {α : Type} {x : α} {Γ Γ' : List α}[ext : Extract x Γ Γ'] :
  ExtractList [x] Γ Γ' := ExtractList.cons ExtractList.nil

/-- ExtractList [x] Γ Γ' があれば、型クラス推論で自動的に Extract x Γ Γ₁ として使えるようにする -/
instance instExtractFromExtractListSingleton {α : Type} {x : α} {Γ Γ' : List α} [extl : ExtractList [x] Γ Γ'] : Extract x Γ Γ' := by
  cases extl with
  | cons h' => cases h'; assumption

/-- 任意のリスト L に対し、自分自身から自分自身を抜き出すと空になる -/
instance instExtractListSelf {α : Type} : {L : List α} → ExtractList L L []
| [] => ExtractList.nil
| _ :: _ => ExtractList.cons instExtractListSelf

/-- Extract x Γ Γ' があれば、自動的に PermList (x :: Γ') Γ を推論できるようにする -/
instance instPermListConsFromExtract {α : Type} {x : α} {Γ Γ' : List α} [Extract x Γ Γ'] :
  PermList (x :: Γ') Γ := ExtractList.cons instExtractListSelf

/-- PermList の反射律: 任意のリストは自分自身と並べ替え同値 -/
@[instance_reducible, refl]
def PermList.refl {α : Type} : (L : List α) → PermList L L
| [] => ExtractList.nil
| _ :: xs => ExtractList.cons (PermList.refl xs)

instance instPermListRefl {α : Type} {L : List α} : PermList L L := PermList.refl L

/-- 2つの抜き出しの可換性: y を抜いてから x を抜けるなら、先に x を抜いてから y を抜くこともできる -/
def extract_comm {α : Type} {x y : α} {Γ Γ₀ Γ₀' : List α}
    (hy : Extract y Γ Γ₀) (hx : Extract x Γ₀ Γ₀') :
    Σ Γ', Extract x Γ Γ' × Extract y Γ' Γ₀' :=
  match hy with
  | Extract.head => ⟨_, Extract.there hx, Extract.head⟩
  | Extract.there hy_tail =>
    match hx with
    | Extract.head => ⟨_, Extract.head, hy_tail⟩
    | Extract.there hx' =>
      let ⟨_, h1, h2⟩ := extract_comm hy_tail hx'
      ⟨_, Extract.there h1, Extract.there h2⟩

/-- Γ から Γ₁ を抜いた残りが [x] ならば、x :: Γ₁ は Γ の並び替えである -/
@[instance_reducible]
def permList_cons_from_extractList_singleton {α : Type} {x : α} :
    {Γ₁ : List α} → {Γ : List α} → ExtractList Γ₁ Γ [x] → PermList (x :: Γ₁) Γ
| [], _, ExtractList.nil =>
  ExtractList.cons ExtractList.nil
| y :: _, _, ExtractList.cons (ext := hy) h_tail =>
  match permList_cons_from_extractList_singleton h_tail with
  | ExtractList.cons (ext := hx) h_nil =>
    let ⟨Γ_mid, hx', hy'⟩ := extract_comm hy hx
    have : Extract x _ Γ_mid := hx'
    have : Extract y Γ_mid _ := hy'
    ExtractList.cons (ExtractList.cons h_nil)

/-- 残りが [x] の場合の自動解決 instance -/
instance instPermListConsFromExtractListSingleton {α : Type} {x : α} {Γ₁ Γ : List α}
    [h : ExtractList Γ₁ Γ [x]] :
    PermList (x :: Γ₁) Γ :=
  permList_cons_from_extractList_singleton h

/-- 1個抜き出すと、要素は「抜かれた要素」か「残りの要素」のどちらかになる -/
theorem mem_iff_eq_or_mem_of_extract {α : Type} {x y : α} {Γ Γ' : List α}
    (h : Extract y Γ Γ') : x ∈ Γ ↔ x = y ∨ x ∈ Γ' := by
  induction h with
  | head =>
    simp only [List.mem_cons]
  | there _ ih =>
    simp only [List.mem_cons, ih]
    grind?

/-- リストを抜き出すと、元の要素は「抜かれたリスト」か「残りのリスト」の和集合になる -/
theorem mem_iff_mem_or_mem_of_extractList {α : Type} {x : α} {Γ₁ Γ Γ₂ : List α}
    (h : ExtractList Γ₁ Γ Γ₂) : x ∈ Γ ↔ x ∈ Γ₁ ∨ x ∈ Γ₂ := by
  induction h with
  | nil =>
    simp only [List.not_mem_nil, false_or]
  | cons h_tail ih =>
    rename_i ext
    rw [mem_iff_eq_or_mem_of_extract ext, ih, List.mem_cons]
    grind?

/-- PermList は要素の所属関係（∈）を完全に保存する -/
theorem mem_of_permList {α : Type} {x : α} {Γ₁ Γ₂ : List α} [h : PermList Γ₁ Γ₂] :
    x ∈ Γ₁ ↔ x ∈ Γ₂ := by
  have := mem_iff_mem_or_mem_of_extractList (x := x) h
  simp only [List.not_mem_nil, or_false] at this
  exact this.symm

/-- 任意の述語 P に対する全称量化（∀ x ∈ Γ, P x）も PermList で保存される -/
theorem all_of_permList {α : Type} {P : α → Prop} {Γ₁ Γ₂ : List α} [PermList Γ₁ Γ₂] :
    (∀ x ∈ Γ₁, P x) ↔ (∀ x ∈ Γ₂, P x) := by
  constructor
  · intro h x hx
    exact h x (mem_of_permList.mpr hx)
  · intro h x hx
    exact h x (mem_of_permList.mp hx)
