/- De que axiomas depende cada funcion de la STF.

   Correr con:  lake env lean RevisarAxiomas.lean
-/
import MiniStf

#print axioms mini_stf.stf.state_transition
#print axioms mini_stf.stf.process_slots
#print axioms mini_stf.stf.process_block
#print axioms mini_stf.stf.process_block_header
#print axioms mini_stf.stf.is_valid_vote
#print axioms mini_stf.stf.slot_is_justifiable_after
#print axioms mini_stf.stf.attestation_data_matches_chain
#print axioms mini_stf.stf.is_proposer
#print axioms mini_stf.stf.current_proposer
#print axioms mini_stf.justified_slots_ops.is_slot_justified
#print axioms mini_stf.justified_slots_ops.set_justified
#print axioms mini_stf.justified_slots_ops.extend_to_slot
#print axioms mini_stf.justified_slots_ops.shift_window
