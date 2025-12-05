asm NeedhamSchroederSpy_Fuzzer

import ../../STDL/StandardLibrary
import ./NeedhamSchroederSpy_signatureAndRules

signature:	
	// To measure some observed behavior of the simulated model
	controlled terminatedProtocols: Integer
	// ------- SIMULATION SIGNATURE --------------- 
	controlled errorExitCode: Integer
	controlled steps: Integer 
	controlled run: Integer
	derived invariant1: Boolean
	derived invariant2: Boolean
	derived invariant3: Boolean
	derived invariant4: Boolean
	derived terminatedRun: Boolean
	static maxRun: Integer
	static maxStep: Integer

definitions:
	// FUNCTION DEFINITIONS
	function maxRun = 1000 	
	function maxStep = 32
	function terminatedRun = terminatedSession = maxProtocolRuns or steps>=maxStep
	// Functions for invariants (we translated invariants of simulated model into derived boolean functions)
	
	// test the model implementation of the protocol
	// each user that is not spy shouldn't send the same nonce to different users //maxProtocolRuns = 1 implies 
	function invariant1 = not(exist $s in UserID with isSpy($s) = FALSE and (exist $r1 in UserID with (exist $r2 in UserID with 
		$r1 != $r2 and (exist $n in Nonce with (hasSentTo($s,$n) = $r1 and hasSentTo($s,$n) = $r2))
	)))
	
	// test both correct model implementation and protocol correctness
	function invariant2 = terminatedSession <= startedSessions
	
	// test protocol property: check confidentiality when the protocol finished at least one time
	function invariant3 =  terminatedSession >= 1 implies not(exist $u1 in UserID with (exist $u2 in UserID with (exist $u3 in UserID with (
		$u1!=$u2 and $u3!=$u1 and $u3!=$u2 and (exist $n1 in Nonce with(exist $n2 in Nonce with $n1!=$n2 and
			knowNonce($u1,$n1)=TRUE and knowNonce($u2,$n1)=TRUE and knowNonce($u3,$n1)=TRUE and knowNonce($u1,$n2)=TRUE and knowNonce($u2,$n2)=TRUE and knowNonce($u3,$n2)=TRUE
		))
	))))
	
	// test protocol property: check correctness of the delivery when the protocol end for the first time
	function invariant4 = (terminatedSession = 1 implies 
		(exist $u1 in UserID with  
			(exist $u2 in UserID with 
				($u1 != $u2 and (exist $n1 in Nonce with 
						(exist $n2 in Nonce with 
							($n1 != $n2 and knowNonce($u1,$n1) = TRUE and knowNonce($u1,$n2) = TRUE and knowNonce($u2,$n1) = TRUE and knowNonce($u2,$n2) = TRUE)
						)
					)
				)
			)
		)
	)
	
	// RULE DEFINITIONS		
	rule r_reinitializeSimulatedModel =
		par
			startedSessions := 0
			terminatedSession := 0
			forall $u in UserID with true do 
				par
					hasAlreadySent($u) := FALSE
					forall $n in Nonce with true do 
						par
							knowNonce($u, $n) := FALSE
							hasSentTo($u, $n) := undef
						endpar
				endpar
			forall $n1 in Nonce with true do isNonceArrivedToReceiver($n1) := FALSE
			forall $m in MessageID do 
				par
					comunication($m) := (undef, undef, undef) 
					hasBeenRead($m) := undef
					messageType($m) := undef
					messageNUK($m) := (undef, undef, undef) 
					messageNNK($m) := (undef, undef, undef) 
					messageNK($m) := (undef, undef) 
				endpar
			steps := 0
		endpar
		
	rule r_simulatedMain = 
		choose $u in UserID with true do
			if isSpy($u) = TRUE then
				r_behaveRandomly[$u] // r_behaveCorrectly[$u]
			else
				r_behaveCorrectly[$u]
			endif
	
	// MAIN RULE	
	main rule r_Main = 
		// initialize simulated model for the first execution
		if run = -1 then
			par
				r_reinitializeSimulatedModel[]
				run := 1
			endpar
		// stop simulation when detecting one error
		else if errorExitCode != 0 then	skip
		// check invariants
		else if not(invariant1) then errorExitCode := 1
		else if not(invariant2) then errorExitCode := 2
		else if not(invariant3) then errorExitCode := 3
		else if not(invariant4) then errorExitCode := 4
		else 			
		// do one transition in the simulated model
			if not(terminatedRun) then 
				par
					steps := steps +1 
					r_simulatedMain[]
				endpar
		// reset the simulated model and simulate again
			else
				if run < maxRun then
					par
						if terminatedSession = 1 then
							terminatedProtocols := terminatedProtocols +1
						endif
						run := run + 1
						r_reinitializeSimulatedModel[]
					endpar
				endif
			endif
		endif endif endif endif endif endif
		
// INITIAL STATE
default init s0:
	// not mandatory, it saves statistics on simulations
	function terminatedProtocols = 0 
	// -------- SIMULATOR INIZIALIZATION ------------------
	function steps = 0 
	function run = -1
	function errorExitCode = 0
