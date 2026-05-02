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

machine Ferry2
sees
context_ferry2

variables
booking_tiket
booking_data_base
set_id_reservation
voiture1 voiture2
pont1 pont2 pont3
set_of_vehicle_on_bridge
set_of_vehicle_book_space
available_space_on_bridge
size_of_vehicle



invariants
	@inv1 booking_tiket ∈ Vehicule ⇸ Id_reservation
	@inv2  booking_data_base ⊆ Vehicule ×(Pont × Id_reservation)
	@inv3  set_id_reservation ⊆ Id_reservation
	@inv4 (voiture1 ∈ Vehicule ) ∧ (voiture2 ∈ Vehicule )
	@inv5 (pont1 ∈ Pont) ∧( pont2 ∈ Pont) ∧ (pont3 ∈ Pont)
	@inv6 set_of_vehicle_on_bridge ∈ Pont → ℙ(Vehicule )
	@inv8 set_of_vehicle_book_space ⊆ Vehicule
	@inv9 available_space_on_bridge ∈ Pont → ℕ
	@inv10 size_of_vehicle ∈ Vehicule → ℕ


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
        @act13 size_of_vehicle ≔ { x ↦ 1 ∣ x ∈ Voiture } ∪ { y ↦ 3 ∣ y ∈ Camion }
  end
  event booking_space_on_boat_update
  	any v p num_reservation
  	where
  		@grd1 v ∈ Vehicule
  		@grd2 v ∉ dom(booking_tiket)
  		@grd3 p ∈ Pont
  		@grd4 num_reservation ∈ Id_reservation
  		@grd5 num_reservation ∉ set_id_reservation
  		@grd6 available_space_on_bridge(p)>0
  		@grd7 available_space_on_bridge(p) − size_of_vehicle(v) ≥ 0

  	then
  		@act1 booking_tiket ≔ booking_tiket ∪ {v ↦ num_reservation}
  		@act2 booking_data_base≔booking_data_base ∪ {v↦(p↦num_reservation)}
  		@act3 set_id_reservation≔set_id_reservation ∪ {num_reservation}
  		@act4 set_of_vehicle_book_space≔set_of_vehicle_book_space ∪ {v}
  		@act5 available_space_on_bridge(p)≔available_space_on_bridge(p)−
  															size_of_vehicle(v)


  end
  event check_and_embark_voiture
   any v p
   where
   		@grd1 v ∈ Voiture ∧  (v ∈ dom(booking_tiket))
  		@grd2 booking_tiket(v)∈ Id_reservation
  		@grd4 p ∈ Pont
  		@grd5 v↦(p↦booking_tiket(v)) ∈ booking_data_base
        @grd6 v ∈ set_of_vehicle_book_space
  		@grd7 card(set_of_vehicle_on_bridge(p))< max_capacity_pont
  		@grd8 booking_data_base ≠ ∅
  		@grd9 set_of_vehicle_book_space ∩ Camion = ∅

   then
        @act1 set_of_vehicle_on_bridge(p)≔ set_of_vehicle_on_bridge(p) ∪ {v}
        @act2 set_of_vehicle_book_space≔set_of_vehicle_book_space ∖ {v}
  end

  event check_and_embark_camion
   any v p
   where
   		@grd1 v ∈ Camion ∧  (v ∈ dom(booking_tiket))
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


<!-- Fin M2 -->




<!-- M3 -->

machine Ferry3
sees
context_ferry2

variables
booking_tiket
booking_data_base
set_id_reservation
voiture1 voiture2
pont1 pont2 pont3
set_of_vehicle_on_bridge
set_of_vehicle_book_space
available_space_on_bridge
size_of_vehicle
monte_charge
end_embark


invariants
	@inv1 booking_tiket ∈ Vehicule ⇸ Id_reservation
	@inv2  booking_data_base ⊆ Vehicule ×(Pont × Id_reservation)
	@inv3  set_id_reservation ⊆ Id_reservation
	@inv4 (voiture1 ∈ Vehicule ) ∧ (voiture2 ∈ Vehicule )
	@inv5 (pont1 ∈ Pont) ∧( pont2 ∈ Pont) ∧ (pont3 ∈ Pont)
	@inv6 set_of_vehicle_on_bridge ∈ Pont → ℙ(Vehicule )
	@inv8 set_of_vehicle_book_space ⊆ Vehicule
	@inv9 available_space_on_bridge ∈ Pont → ℕ
	@inv10 size_of_vehicle ∈ Vehicule → ℕ
	@inv11 monte_charge ⊆ Vehicule
	@inv12 end_embark ∈ BOOL


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
        @act13 size_of_vehicle ≔ { x ↦ 1 ∣ x ∈ Voiture } ∪ { y ↦ 3 ∣ y ∈ Camion }
        @act14 monte_charge≔∅
        @act15 end_embark ≔ TRUE
  end
  event booking_space_on_boat_update
  	any v p num_reservation
  	where
  		@grd1 v ∈ Vehicule
  		@grd2 v ∉ dom(booking_tiket)
  		@grd3 p ∈ Pont
  		@grd4 num_reservation ∈ Id_reservation
  		@grd5 num_reservation ∉ set_id_reservation
  		@grd6 available_space_on_bridge(p)>0
  		@grd7 available_space_on_bridge(p) − size_of_vehicle(v) ≥ 0

  	then
  		@act1 booking_tiket ≔ booking_tiket ∪ {v ↦ num_reservation}
  		@act2 booking_data_base≔booking_data_base ∪ {v↦(p↦num_reservation)}
  		@act3 set_id_reservation≔set_id_reservation ∪ {num_reservation}
  		@act4 set_of_vehicle_book_space≔set_of_vehicle_book_space ∪ {v}
  		@act5 available_space_on_bridge(p)≔available_space_on_bridge(p)−
  															size_of_vehicle(v)


  end
  event voiture_to_monte_charge
   any v
   where
   		@grd1 v ∈ Voiture ∧  (v ∈ dom(booking_tiket))
  		@grd2 booking_tiket(v)∈ Id_reservation
        @grd3 v ∈ set_of_vehicle_book_space
  		@grd4 (card(monte_charge ∩ Voiture)+ 3∗card(monte_charge ∩ Camion))+1 ≤ max_monte_charge
  		@grd5 booking_data_base ≠ ∅
  		@grd6 set_of_vehicle_book_space ∩ Camion = ∅
  		@grd7 end_embark = TRUE

   then
        @act1 monte_charge≔monte_charge ∪ {v}
        @act2 set_of_vehicle_book_space≔set_of_vehicle_book_space ∖ {v}
  end

  event  camion_to_monte_charge
   any v
   where
   		@grd1 v ∈ Camion ∧  (v ∈ dom(booking_tiket))
  		@grd2 booking_tiket(v)∈ Id_reservation
        @grd6 v ∈ set_of_vehicle_book_space
  		@grd7 (card(monte_charge ∩ Voiture)+ 3∗card(monte_charge ∩ Camion))+3 ≤ max_monte_charge
  		@grd8 booking_data_base ≠ ∅
  		@grd9 end_embark = TRUE
   then
        @act1 monte_charge≔ monte_charge ∪ {v}
        @act2 set_of_vehicle_book_space≔set_of_vehicle_book_space ∖ {v}
  end


  event monte_charge_to_pont
   any v p
   where
           @grd1 v ∈ Vehicule
        @grd3 v ∈ monte_charge
          @grd2 booking_tiket(v)∈ Id_reservation
          @grd4 p ∈ Pont
          @grd5 v↦(p↦booking_tiket(v)) ∈ booking_data_base
          @grd6 card(monte_charge)>0
          @grd7 max_capacity_pont − card(set_of_vehicle_on_bridge(p)) ≥ (card(monte_charge ∩ Voiture)
                                                                                      + 3∗card(monte_charge ∩ Camion))
   then

        @act1 set_of_vehicle_on_bridge(p)≔ set_of_vehicle_on_bridge(p) ∪ {v}
        @act2 monte_charge≔ monte_charge ∖ {v}
        @act3 end_embark≔ FALSE
  end

    event move_monte_charge_down
   where
   		@grd1 monte_charge = ∅
   		@grd2 end_embark= FALSE
   then
        @act1 end_embark≔ TRUE
  end
end
<!-- Fin M3 -->


<!-- M4 -->


machine Ferry4
sees
context_ferry2

variables
booking_tiket
booking_data_base
set_id_reservation
voiture1 voiture2
pont1 pont2 pont3
set_of_vehicle_on_bridge
set_of_vehicle_book_space
available_space_on_bridge
size_of_vehicle
monte_charge
end_embark
barrieres
capteurs
pont_cible
position_montecharge


invariants
	@inv1 booking_tiket ∈ Vehicule ⇸ Id_reservation
	@inv2  booking_data_base ⊆ Vehicule ×(Pont × Id_reservation)
	@inv3  set_id_reservation ⊆ Id_reservation
	@inv4 (voiture1 ∈ Vehicule ) ∧ (voiture2 ∈ Vehicule )
	@inv5 (pont1 ∈ Pont) ∧( pont2 ∈ Pont) ∧ (pont3 ∈ Pont)
	@inv6 set_of_vehicle_on_bridge ∈ Pont → ℙ(Vehicule )
	@inv8 set_of_vehicle_book_space ⊆ Vehicule
	@inv9 available_space_on_bridge ∈ Pont → ℕ
	@inv10 size_of_vehicle ∈ Vehicule → ℕ
	@inv11 monte_charge ⊆ Vehicule
	@inv12 end_embark ∈ BOOL
	@inv13 barrieres ∈ BOOL
	@inv14 capteurs ∈ BOOL
	@inv15 pont_cible ∈ Pont
	@inv16 position_montecharge ∈ Pont

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
        @act13 size_of_vehicle ≔ { x ↦ 1 ∣ x ∈ Voiture } ∪ { y ↦ 3 ∣ y ∈ Camion }
        @act14 monte_charge≔∅
        @act15 end_embark ≔ TRUE
        @act16 barrieres ≔ FALSE
        @act17 capteurs ≔ FALSE
        @act18 pont_cible ≔ p1
        @act19 position_montecharge ≔ p1

  end
  event booking_space_on_boat_update
  	any v p num_reservation
  	where
  		@grd1 v ∈ Vehicule
  		@grd2 v ∉ dom(booking_tiket)
  		@grd3 p ∈ Pont
  		@grd4 num_reservation ∈ Id_reservation
  		@grd5 num_reservation ∉ set_id_reservation
  		@grd6 available_space_on_bridge(p)>0
  		@grd7 available_space_on_bridge(p) − size_of_vehicle(v) ≥ 0

  	then
  		@act1 booking_tiket ≔ booking_tiket ∪ {v ↦ num_reservation}
  		@act2 booking_data_base≔booking_data_base ∪ {v↦(p↦num_reservation)}
  		@act3 set_id_reservation≔set_id_reservation ∪ {num_reservation}
  		@act4 set_of_vehicle_book_space≔set_of_vehicle_book_space ∪ {v}
  		@act5 available_space_on_bridge(p)≔available_space_on_bridge(p)−
  															size_of_vehicle(v)



  end
  event voiture_to_monte_charge
   any v p
   where
   		@grd1 v ∈ Voiture
   		@grd10 (v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base)
  		@grd2 booking_tiket(v)∈ Id_reservation
        @grd3 v ∈ set_of_vehicle_book_space
  		@grd4 (card(monte_charge ∩ Voiture)+ 3∗card(monte_charge ∩ Camion))+1 ≤ max_monte_charge
  		@grd5 booking_data_base ≠ ∅
  		@grd6 set_of_vehicle_book_space ∩ Camion = ∅
  		@grd7 end_embark = TRUE
  		@grd8 barrieres = TRUE
  		@grd9 p ∈ Pont

   then
        @act1 monte_charge≔monte_charge ∪ {v}
        @act2 set_of_vehicle_book_space≔set_of_vehicle_book_space ∖ {v}

  end

  event  camion_to_monte_charge
   any v p
   where
   		@grd1 v ∈ Camion
   		@grd10 (v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base)
  		@grd2 booking_tiket(v)∈ Id_reservation
        @grd6 v ∈ set_of_vehicle_book_space
  		@grd7 (card(monte_charge ∩ Voiture)+ 3∗card(monte_charge ∩ Camion))+3 ≤ max_monte_charge
  		@grd8 booking_data_base ≠ ∅
  		@grd9 end_embark = TRUE
  		@grd3 barrieres = TRUE
  		@grd4 p ∈ Pont

   then
        @act1 monte_charge≔ monte_charge ∪ {v}
        @act2 set_of_vehicle_book_space≔set_of_vehicle_book_space ∖ {v}

  end

  event monte_charge_up_to_pont
    any p v
    where
    	@grd1 p ∈ Pont
        @grd2 v ∈ monte_charge
        @grd3 end_embark = FALSE
        @grd4 barrieres = FALSE
        @grd5 v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base
        @grd6 card(monte_charge) > 0

    then
        @act1 pont_cible ≔ p
        @act2 capteurs ≔ FALSE
    end

   event monte_charge_arrives
    where
        @grd1 pont_cible ≠ position_montecharge
        @grd2 capteurs = FALSE
        @grd3 card(monte_charge) > 0
        @grd4 barrieres = FALSE
        @grd5 end_embark = FALSE
    then
        @act1 position_montecharge ≔ pont_cible
    end

   event capteurs_detecte_alignement
    where
        @grd1 position_montecharge = pont_cible
        @grd2 capteurs = FALSE
        @grd3 card(monte_charge) > 0
        @grd4 barrieres = FALSE
        @grd5 end_embark = FALSE
    then
        @act1 capteurs ≔ TRUE
    end

  event monte_charge_to_pont
   any v p
   where
          @grd1 v ∈ Vehicule
          @grd3 v ∈ monte_charge
          @grd2 booking_tiket(v)∈ Id_reservation
          @grd4 p ∈ Pont
          @grd5 v↦(p↦booking_tiket(v)) ∈ booking_data_base
          @grd6 card(monte_charge)>0
          @grd8 barrieres = TRUE
          @grd7 max_capacity_pont − card(set_of_vehicle_on_bridge(p)) ≥ (card(monte_charge ∩ Voiture)
                                                                                      + 3∗card(monte_charge ∩ Camion))
          @grd9 p=pont_cible

   then

        @act1 set_of_vehicle_on_bridge(p)≔ set_of_vehicle_on_bridge(p) ∪ {v}
        @act2 monte_charge≔ monte_charge ∖ {v}
        @act3 end_embark≔ FALSE
  end

    event move_monte_charge_down
   where
   		@grd1 monte_charge = ∅
   		@grd2 end_embark= FALSE
   		@grd3 barrieres = FALSE
   then
        @act1 end_embark≔ TRUE
  end

  event on_barrieres_embarquement
	where
	    @grd1 barrieres = FALSE
	    @grd2 set_of_vehicle_book_space ≠ ∅
	    @grd3 card(monte_charge) = 0
	    @grd4 end_embark = TRUE
	then
	    @act1 barrieres ≔ TRUE
	end

	event on_barrieres_debarquement
	where
	    @grd1 barrieres = FALSE
	    @grd2 capteurs = TRUE
	    @grd3 card(monte_charge) > 0
	    @grd4 end_embark = FALSE
	then
	    @act1 barrieres ≔ TRUE
	end

  event off_barrieres_embarquement
	where
	    @grd1 barrieres = TRUE
	    @grd2 end_embark = TRUE
	    @grd3 card(monte_charge) > 0
	then
	    @act1 barrieres ≔ FALSE
	    @act2 end_embark ≔ FALSE
	end

	event off_barrieres_debarquement
	where
	    @grd1 barrieres = TRUE
	    @grd2 end_embark = FALSE
	then
	    @act1 barrieres ≔ FALSE
	    @act2 capteurs ≔ FALSE
	end


end


:<!-- Fin M4 -->


<!-- M5 -->
machine Ferry5
sees
context_ferry2
 
variables
booking_tiket
booking_data_base
set_id_reservation
voiture1 voiture2
pont1 pont2 pont3
set_of_vehicle_on_bridge
set_of_vehicle_book_space
available_space_on_bridge
size_of_vehicle
monte_charge
end_embark
barrieres
capteurs
pont_cible
position_montecharge
file1
file2
notifications
 
invariants
	@inv1  booking_tiket ∈ Vehicule ⇸ Id_reservation
	@inv2  booking_data_base ⊆ Vehicule × (Pont × Id_reservation)
	@inv3  set_id_reservation ⊆ Id_reservation
	@inv4  (voiture1 ∈ Vehicule) ∧ (voiture2 ∈ Vehicule)
	@inv5  (pont1 ∈ Pont) ∧ (pont2 ∈ Pont) ∧ (pont3 ∈ Pont)
	@inv6  set_of_vehicle_on_bridge ∈ Pont → ℙ(Vehicule)
	@inv8  set_of_vehicle_book_space ⊆ Vehicule
	@inv9  available_space_on_bridge ∈ Pont → ℕ
	@inv10 size_of_vehicle ∈ Vehicule → ℕ
	@inv11 monte_charge ⊆ Vehicule
	@inv12 end_embark ∈ BOOL
	@inv13 barrieres ∈ BOOL
	@inv14 capteurs ∈ BOOL
	@inv15 pont_cible ∈ Pont
	@inv16 position_montecharge ∈ Pont
	@inv17 file1 ⊆ Vehicule
	@inv18 file2 ⊆ Vehicule
	@inv19 file1 ∩ file2 = ∅
	@inv20 notifications ∈ Vehicule ⇸ Message
 
events
 
  event INITIALISATION
  	then
  		@act1  booking_tiket ≔ ∅
  		@act2  booking_data_base ≔ ∅
  		@act3  voiture1 ≔ v1
  		@act4  voiture2 ≔ v2
  		@act5  pont1 ≔ p1
  		@act6  pont2 ≔ p2
  		@act7  pont3 ≔ p3
  		@act8  set_id_reservation ≔ ∅
  		@act9  set_of_vehicle_on_bridge ≔ {p1 ↦ ∅, p2 ↦ ∅, p3 ↦ ∅}
  		@act11 set_of_vehicle_book_space ≔ ∅
  		@act12 available_space_on_bridge ≔ {p1 ↦ max_capacity_pont, p2 ↦ max_capacity_pont, p3 ↦ max_capacity_pont}
  		@act13 size_of_vehicle ≔ {x ↦ 1 ∣ x ∈ Voiture} ∪ {y ↦ 3 ∣ y ∈ Camion}
  		@act14 monte_charge ≔ ∅
  		@act15 end_embark ≔ TRUE
  		@act16 barrieres ≔ FALSE
  		@act17 capteurs ≔ FALSE
  		@act18 pont_cible ≔ p1
  		@act19 position_montecharge ≔ p1
  		@act20 file1 ≔ ∅
  		@act21 file2 ≔ ∅
  		@act22 notifications ≔ ∅
  end
 
  event booking_space_on_boat_update
  	any v p num_reservation
  	where
  		@grd1 v ∈ Vehicule
  		@grd2 v ∉ dom(booking_tiket)
  		@grd3 p ∈ Pont
  		@grd4 num_reservation ∈ Id_reservation
  		@grd5 num_reservation ∉ set_id_reservation
  		@grd6 available_space_on_bridge(p) > 0
  		@grd7 available_space_on_bridge(p) − size_of_vehicle(v) ≥ 0
  	then
  		@act1 booking_tiket ≔ booking_tiket ∪ {v ↦ num_reservation}
  		@act2 booking_data_base ≔ booking_data_base ∪ {v ↦ (p ↦ num_reservation)}
  		@act3 set_id_reservation ≔ set_id_reservation ∪ {num_reservation}
  		@act4 set_of_vehicle_book_space ≔ set_of_vehicle_book_space ∪ {v}
  		@act5 available_space_on_bridge(p) ≔ available_space_on_bridge(p) − size_of_vehicle(v)
  end
 
  event borne_lecture_camion
  	any v
  	where
  		@grd1 v ∈ Camion
  		@grd2 v ∈ dom(booking_tiket)
  		@grd3 v ∉ file1
  		@grd4 v ∉ file2
  	then
  		@act1 file1 ≔ file1 ∪ {v}
  end
 
  event borne_lecture_voiture
  	any v
  	where
  		@grd1 v ∈ Voiture
  		@grd2 v ∈ dom(booking_tiket)
  		@grd3 v ∉ file1
  		@grd4 v ∉ file2
  	then
  		@act1 file2 ≔ file2 ∪ {v}
  end
 
  event camion_to_monte_charge
   any v p
   where
   		@grd1  v ∈ Camion
   		@grd10 v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base
  		@grd2  booking_tiket(v) ∈ Id_reservation
        @grd6  v ∈ set_of_vehicle_book_space
        @grd11 v ∈ file1
  		@grd7  (card(monte_charge ∩ Voiture) + 3 ∗ card(monte_charge ∩ Camion)) + 3 ≤ max_monte_charge
  		@grd8  booking_data_base ≠ ∅
  		@grd9  end_embark = TRUE
  		@grd3  barrieres = TRUE
  		@grd4  p ∈ Pont
   then
        @act1 monte_charge ≔ monte_charge ∪ {v}
        @act2 set_of_vehicle_book_space ≔ set_of_vehicle_book_space ∖ {v}
        @act3 file1 ≔ file1 ∖ {v}
  end
 
  event voiture_to_monte_charge
   any v p
   where
   		@grd1  v ∈ Voiture
   		@grd10 v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base
  		@grd2  booking_tiket(v) ∈ Id_reservation
        @grd3  v ∈ set_of_vehicle_book_space
        @grd11 v ∈ file2
  		@grd4  (card(monte_charge ∩ Voiture) + 3 ∗ card(monte_charge ∩ Camion)) + 1 ≤ max_monte_charge
  		@grd5  booking_data_base ≠ ∅
  		@grd6  set_of_vehicle_book_space ∩ Camion = ∅
  		@grd7  end_embark = TRUE
  		@grd8  barrieres = TRUE
  		@grd9  p ∈ Pont
   then
        @act1 monte_charge ≔ monte_charge ∪ {v}
        @act2 set_of_vehicle_book_space ≔ set_of_vehicle_book_space ∖ {v}
        @act3 file2 ≔ file2 ∖ {v}
  end
 
  event monte_charge_up_to_pont
    any p v
    where
    	@grd1 p ∈ Pont
        @grd2 v ∈ monte_charge
        @grd3 end_embark = FALSE
        @grd4 barrieres = FALSE
        @grd5 v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base
        @grd6 card(monte_charge) > 0
    then
        @act1 pont_cible ≔ p
        @act2 capteurs ≔ FALSE
    end
 
   event monte_charge_arrives
    where
        @grd1 pont_cible ≠ position_montecharge
        @grd2 capteurs = FALSE
        @grd3 card(monte_charge) > 0
        @grd4 barrieres = FALSE
        @grd5 end_embark = FALSE
    then
        @act1 position_montecharge ≔ pont_cible
    end
 
   event capteurs_detecte_alignement
    where
        @grd1 position_montecharge = pont_cible
        @grd2 capteurs = FALSE
        @grd3 card(monte_charge) > 0
        @grd4 barrieres = FALSE
        @grd5 end_embark = FALSE
    then
        @act1 capteurs ≔ TRUE
    end
 
  event monte_charge_to_pont
   any v p
   where
          @grd1 v ∈ Vehicule
          @grd3 v ∈ monte_charge
          @grd2 booking_tiket(v) ∈ Id_reservation
          @grd4 p ∈ Pont
          @grd5 v ↦ (p ↦ booking_tiket(v)) ∈ booking_data_base
          @grd6 card(monte_charge) > 0
          @grd8 barrieres = TRUE
          @grd7 max_capacity_pont − card(set_of_vehicle_on_bridge(p)) ≥ (card(monte_charge ∩ Voiture) + 3 ∗ card(monte_charge ∩ Camion))
          @grd9 p = pont_cible
   then
        @act1 set_of_vehicle_on_bridge(p) ≔ set_of_vehicle_on_bridge(p) ∪ {v}
        @act2 monte_charge ≔ monte_charge ∖ {v}
        @act3 end_embark ≔ FALSE
        @act4 notifications ≔ notifications ∪ {v ↦ you_can_move}
  end
 
  event conducteur_recoit_notification
   any v
   where
        @grd1 v ∈ dom(notifications)
        @grd2 v ∈ dom(booking_tiket)
   then
        @act1 notifications ≔ {v} ⩤ notifications
  end
 
  event move_monte_charge_down
   where
   		@grd1 monte_charge = ∅
   		@grd2 end_embark = FALSE
   		@grd3 barrieres = FALSE
   then
        @act1 end_embark ≔ TRUE
  end
 
  event on_barrieres_embarquement
	where
	    @grd1 barrieres = FALSE
	    @grd2 set_of_vehicle_book_space ≠ ∅
	    @grd3 card(monte_charge) = 0
	    @grd4 end_embark = TRUE
	then
	    @act1 barrieres ≔ TRUE
	end
 
	event on_barrieres_debarquement
	where
	    @grd1 barrieres = FALSE
	    @grd2 capteurs = TRUE
	    @grd3 card(monte_charge) > 0
	    @grd4 end_embark = FALSE
	then
	    @act1 barrieres ≔ TRUE
	end
 
  event off_barrieres_embarquement
	where
	    @grd1 barrieres = TRUE
	    @grd2 end_embark = TRUE
	    @grd3 card(monte_charge) > 0
	then
	    @act1 barrieres ≔ FALSE
	    @act2 end_embark ≔ FALSE
	end
 
	event off_barrieres_debarquement
	where
	    @grd1 barrieres = TRUE
	    @grd2 end_embark = FALSE
	then
	    @act1 barrieres ≔ FALSE
	    @act2 capteurs ≔ FALSE
	end
 
end


<!-- Fin M5 -->

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

context context_ferry2

sets Vehicule Pont Id_reservation

constants

  v1 v2 v3 v4 v5 v6
  c1  c2 c3 c4 c5 c6
  p1 p2 p3
  i12 i23 i13 i22 i33
  i10 i21 i30 i14 i20 i38
  i17 i24 i31 i19 i28 i35
  i25 i36 i18 i29 i32 i16 i55
  max_capacity_pont max_monte_charge  Voiture Camion


axioms
  @axm1 (Voiture ⊆ Vehicule) ∧ (Camion ⊆ Vehicule )
  @axm2 partition(Voiture,{v1},{v2},{v3},{v4},{v5},{v6})
  @axm3 partition(Camion,{c1},{c2},{c3},{c4},{c5},{c6})
  @axm4 partition(Vehicule,Camion ,Voiture)
  @axm5 partition(Pont,{p1},{p2},{p3})
  @axm6 (max_capacity_pont ∈ ℕ) ∧ (max_monte_charge ∈ ℕ)
  @axm7 max_capacity_pont=8
  @axm8 max_monte_charge=6
  @axm9 partition(Id_reservation,{i12},{i23},{i13},{i22},{i33}
  											,{i16},{i25},{i36},{i18},{i29},{i32},
  													{i10},{i21},{i30},{i14},{i20},{i38},
  														{i17},{i24},{i31},{i19},{i28},{i35},{i55})
end

<!--------------------  Fin C2 -------------------->




<!--------------------  C3 ------------------------>


code


<!--------------------  Fin C3 -------------------->
