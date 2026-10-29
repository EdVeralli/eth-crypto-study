/- De que axiomas depende cada funcion de la STF.

   Correr con:  lake env lean RevisarAxiomas.lean
-/
import MiniStf

#print axioms stf.state_transition
#print axioms stf.process_slots
#print axioms stf.process_block
#print axioms stf.process_block_header
#print axioms stf.is_valid_vote
#print axioms stf.slot_is_justifiable_after
#print axioms stf.attestation_data_matches_chain
#print axioms stf.is_proposer
#print axioms stf.current_proposer
#print axioms justified_slots_ops.is_slot_justified
#print axioms justified_slots_ops.set_justified
#print axioms justified_slots_ops.extend_to_slot
#print axioms justified_slots_ops.shift_window
