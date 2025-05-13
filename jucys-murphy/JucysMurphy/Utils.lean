import Mathlib

open Equiv




noncomputable section

abbrev S (n : ℕ) := Perm (Fin n)
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)



#check Equiv.Perm.viaFintypeEmbedding

/-
  Tavat jotenka formalisoida ℂ [S (n-1)]:
    - Tämä on alimoduuli jolla on algebran rakenne: SAADAAN HALUTUSTA
    - Tämä on alialgebra: SAADAAN HALUTUSTA

  Halutaan:
    - Tämä on MonoidAlgebra ja meillä on embedding φ: ℂ[S n], joka on algebra homomorfismi!!!
    - Halutaan että φ myös (i j) ↦ (i j) ihan vaan käytännön vuoks

  Tarvitaan:
    - Todistus että lift on algebra homomorfismi + injektio: riittää että aiempi lift on ryhmähomomorfismi ja inj.
    - Määritellään jokaiselle ℂ[S n] omat jmElem (parempi ois joku kategoriateoreettinen limit rakenne) ja sit näytetään
      että lift mäppää nämä toisiinsa.
-/

/-
  Toinen tapa tehdä lift: ensin luvuille `Fin.castLEEmb`, sitte ryhmille `Equiv.Perm.viaFintypeEmbedding` ja sitte Inton käyttämä `MonoidAlgebra.mapDomain`
  Jotta saadaan homomorfismi: ensin sama, sitte `Equiv.Perm.viaEmbeddingHom` ja sitte ???
-/

-- Paljon juttuja löytyy Equiv.Fintype!

#check Fin.castLEEmb  -- lift luvuille suoraan, ei erillistä funktiota tälle
-- Embedding, eli tähän on built in injectiivisyys

--def lift_sym'' (m : ℕ) (σ : S n) (h_leq : n ≤ m) : S m := Equiv.Perm.viaFintypeEmbedding σ (Fin.castLEEmb h_leq) -- homomorfismiversio???
--def lift_mon'' {m : ℕ} (v : MonoidAlgebra ℂ (S n)) (h_leq : n ≤ m) : MonoidAlgebra ℂ (S m) := MonoidAlgebra.mapDomain (lift_sym' n m ?_ h_leq) v



-- Erikoistettu versio normi symmetrisille ryhmille

-- HETKONEN!!! KÄYTÄ SUORAAN Perm.Fin JUTTUJA!!! EI TARVETTA (S n) → (S m): RITTÄÄ VAAN (S n) → (S (n+1)) JA KOMPOSITIO!

-- VIELÄ YKS TAPA: Käytä sittenkin Finset permutaatioita: tällöin i, j olis elementtejä eikä tarvis coercioita!

#check Equiv.Perm.decomposeFin (swap 0 2)



def lift_sym' {n m : ℕ} (h_leq : n ≤ m) : (S n) →* (S m) := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h_leq)

lemma lift_sym_inj' {n m : ℕ} {h_leq : n ≤ m} : Function.Injective ↑(lift_sym' h_leq) :=
  Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb h_leq)



def lift_mon' {n m : ℕ} (h_leq : n ≤ m) : (A n) →ₐ[ℂ] (A m) := MonoidAlgebra.mapDomainAlgHom ℂ ℂ (lift_sym' h_leq)

lemma lift_mon_inj' {n m : ℕ} {h_leq : n ≤ m} : Function.Injective ↑(lift_mon' h_leq) :=
  Finsupp.mapDomain_injective lift_sym_inj'


#check Fin.castAddEmb
#check Fin.castSuccEmb


def lift_sym {n : ℕ} : S n →* S (n + 1) := Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb)

def lift_mon {n : ℕ} : A n →ₐ[ℂ] A (n + 1) := MonoidAlgebra.mapDomainAlgHom ℂ ℂ lift_sym

-- Tässä kontekstissa voidaan laittaa nää koersioiksi
--instance CoeDep (S n) (S m)...


-- Lemmoja näistä
-- Ehkä tähän lemmat että lift ∘ lift = lift ja lift : A n → A n = id

lemma lift_sym_inj {n : ℕ} : Function.Injective ↑(@lift_sym n) :=
  Equiv.Perm.viaEmbeddingHom_injective (Fin.castAddEmb 1)

lemma lift_mon_inj {n : ℕ} : Function.Injective ↑(@lift_mon n) :=
  Finsupp.mapDomain_injective (@lift_sym_inj n)


@[simp]
lemma natCast_comm_castAdd ↑i

-- Tyypit ei matchaa bruhhh...
@[simp]
lemma lift_sym_comp_lift_sym {n m k : ℕ} {σ : S n} : lift_sym (n + m) k (lift_sym n m σ) = lift_sym n (m + k) σ := by
  sorry

@[simp]
lemma lift_mon_comp_lift_mon {n m k : ℕ} {v : A n} : lift_mon (n + m) k (lift_mon n m v) = lift_mon n (m + k) v := by
  sorry


--


-- Yllättävän hankala
@[simp]
lemma lift_swap_eq_swap {n i j : ℕ} [NeZero n] : swap (↑i) (↑j) = @lift_sym n (swap (↑i) (↑j)) := by
  unfold lift_sym
  rw [Perm.viaEmbeddingHom_apply] -- Rewrite what the lifting actually does
  rw [←Equiv.coe_inj]             -- Only need that the underlying functions match
  funext x

  unfold Perm.viaEmbedding
  simp

  sorry



--@[simp]
--lemma coe_lift_comm {n m : ℕ} {σ : S n} : MonoidAlgebra.of ℂ (S (n + m)) (lift_sym n m σ) =

@[simp]
lemma lift_mon_of_perm_eq_lift_sym {n m : ℕ} {σ : S n} : lift_mon n m (MonoidAlgebra.of ℂ (S n) σ) = MonoidAlgebra.of ℂ (S (n + m)) (lift_sym n m σ) := by
  unfold lift_mon
  simp


def jmElem' (k n : ℕ) [NeZero n] : A n := ∑ i ∈ Finset.Ico 0 (n - 1), MonoidAlgebra.of ℂ (S n) (swap i (k-1))
-- Tarvitaa viel k restricted 2,3,...,n

-- Halutaan että jmElem mäppää toisiinsa
lemma lift_jmElem_eq_jmElem {n m k : ℕ} [NeZero n] [NeZero m]: lift_mon n m (jmElem' k n) = jmElem' k (n + m) := by
  unfold jmElem'
  simp only [Finset.mem_range, map_sum, lift_mon_of_perm_eq_lift_sym]
  sorry
  --apply Finset.sum_equiv Equiv.refl (Fin n) ...




#check Finset.sum_equiv
