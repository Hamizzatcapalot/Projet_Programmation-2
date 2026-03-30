<!--------------------  MACHINE ------------------>
<!-- M1 -->

machine Ferry1
sees
context_ferry1

variables
booking_tiket
booking_data_base
set_id_reservation
voiture1 voiture2
pont1 pont2 pont3
set_of_vehicle_on_bridge
set_of_vehicle_book_space
available_space_on_bridge

invariants
	@inv1 booking_tiket ∈ Vehicule ⇸ Id_reservation
	@inv2  booking_data_base ⊆ Vehicule ×(Pont × Id_reservation)
	@inv3  set_id_reservation ⊆ Id_reservation
	@inv4 (voiture1 ∈ Vehicule ) ∧ (voiture2 ∈ Vehicule )
	@inv5 (pont1 ∈ Pont) ∧( pont2 ∈ Pont) ∧ (pont3 ∈ Pont)
	@inv6 set_of_vehicle_on_bridge ∈ Pont → ℙ(Vehicule )
	@inv8 set_of_vehicle_book_space ⊆ Vehicule
	@inv9 available_space_on_bridge ∈ Pont → ℕ

events
  event INITIALISATION
  	then
  		@act1 booking_tiket≔∅
  		@act2 booking_data_base≔∅
  		@act3 voiture1≔v1
  		@act4 voiture2≔v2
  		@act5 pont1≔p1
  		@act6 pont2≔p2
  		@act7 pont3≔p3
  		@act8 set_id_reservation≔∅
  		@act9 set_of_vehicle_on_bridge≔{p1↦∅, p2↦∅,p3↦∅}
  		@act11 set_of_vehicle_book_space≔∅
  		@act12 available_space_on_bridge≔{p1↦ max_capacity_pont,p2↦max_capacity_pont,p3↦max_capacity_pont}

  end
  event booking_space_on_boat
  	any v p num_reservation
  	where
  		@grd1 v ∈ Vehicule
  		@grd2 v ∉ dom(booking_tiket)
  		@grd3 p ∈ Pont
  		@grd4 num_reservation ∈ Id_reservation
  		@grd5 num_reservation ∉ set_id_reservation
  		@grd6 available_space_on_bridge(p)>0

  	then
  		@act1 booking_tiket ≔ booking_tiket ∪ {v ↦ num_reservation}
  		@act2 booking_data_base≔booking_data_base ∪ {v↦(p↦num_reservation)}
  		@act3 set_id_reservation≔set_id_reservation ∪ {num_reservation}
  		@act4 set_of_vehicle_book_space≔set_of_vehicle_book_space ∪ {v}
  		@act5 available_space_on_bridge(p)≔available_space_on_bridge(p)−1

  end
  event check_and_embark_vehicle
   any v p
   where
   		@grd1 v ∈ Vehicule ∧  (v ∈ dom(booking_tiket))
  		@grd2 booking_tiket(v)∈ Id_reservation
  		@grd4 p ∈ Pont
  		@grd5 v↦(p↦booking_tiket(v)) ∈ booking_data_base
        @grd6 v ∈ set_of_vehicle_book_space
  		@grd7 card(set_of_vehicle_on_bridge(p))< max_capacity_pont
  		@grd8 booking_data_base ≠ ∅
   then
        @act1 set_of_vehicle_on_bridge(p)≔ set_of_vehicle_on_bridge(p) ∪ {v}
        @act2 set_of_vehicle_book_space≔set_of_vehicle_book_space ∖ {v}
  end
end

<!-- Fin M1 -->


<!-- M2 -->

code

<!-- Fin M2 -->




<!-- M3 -->

code
<!-- Fin M3 -->


<!-- M4 -->

code
<!-- Fin M4 -->


<!--------------------  CONTEXTE ------------------>


<!--------------------  C1 ------------------------>

context context_ferry1

sets Vehicule Pont Id_reservation

constants
  v1 v2 v3 v4 v5 v6
  p1 p2 p3
  i12 i23 i13 i22 i33
  i10 i21 i30 i14 i20 i38
  i17 i24 i31 i19 i28 i35
  i25 i36 i18 i29 i32 i16
  max_capacity_pont


axioms
  @axm1 partition(Vehicule,{v1},{v2},{v3},{v4},{v5},{v6})
  @axm2 partition(Pont,{p1},{p2},{p3})
  @axm3 max_capacity_pont ∈ ℕ
  @axm4 max_capacity_pont=3
  @axm5 partition(Id_reservation,{i12},{i23},{i13},{i22},{i33}
  											,{i16},{i25},{i36},{i18},{i29},{i32},
  													{i10},{i21},{i30},{i14},{i20},{i38},
  														{i17},{i24},{i31},{i19},{i28},{i35})
end

<!--------------------  Fin C1 -------------------->



<!--------------------  C2 ------------------------>

code
<!--------------------  Fin C2 -------------------->

