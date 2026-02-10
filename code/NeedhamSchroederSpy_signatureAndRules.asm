
asm NeedhamSchroederSpy_signatureAndRules

import ../../STDL/StandardLibrary
export *

signature:
	enum domain Bool = {TRUE, FALSE}
	enum domain MessageType = {NUK, NNK, NK}
	domain Nonce subsetof Integer
	domain MessageID subsetof Integer
	domain UserID subsetof Integer
	domain PubKeyID subsetof Integer
	domain PrivKeyID subsetof Integer 
	domain SessionNumbers subsetof Integer
	
	controlled startedSessions: SessionNumbers
	controlled terminatedSession: SessionNumbers
	controlled hasAlreadySent: UserID -> Bool
	controlled knowNonce: Prod(UserID, Nonce) -> Bool
	controlled isNonceArrivedToReceiver: Nonce -> Bool
	// without loosing generality, we assume comunication_i = (u_a, u_b, message_i) for all i
	controlled comunication: MessageID -> Prod(UserID, UserID) 
	controlled hasBeenRead: MessageID -> Bool // read by the intended user
	controlled messageType: MessageID -> MessageType
	controlled messageNUK: MessageID -> Prod(Nonce, UserID, PubKeyID)
	controlled messageNNK: MessageID -> Prod(Nonce, Nonce, PubKeyID)
	controlled messageNK: MessageID -> Prod(Nonce, PubKeyID)
	controlled hasSentTo: Prod(UserID, Nonce) -> UserID
	
	derived isFresh: Nonce -> Bool
	derived decryptNUK: Prod(MessageID, PrivKeyID) -> Prod(Nonce, UserID)
	derived decryptNNK: Prod(MessageID, PrivKeyID) -> Prod(Nonce, Nonce)
	derived decryptNK: Prod(MessageID, PrivKeyID) -> Nonce	
	
	static pubKeyFromPrivate: PrivKeyID -> PubKeyID
	static privKeyOf: UserID -> PrivKeyID
	static pubKeyOf: UserID -> PubKeyID
	static ownerOfPrivKey: PrivKeyID -> UserID
	static ownerOfPubKey: PubKeyID -> UserID
	static isSpy: UserID -> Bool
	static maxProtocolRuns: SessionNumbers
	

definitions:
	// DOMAIN DEFINITIONS
	// This is the minimal set configuration needed to accurately model and properly terminate the protocol
//	domain Nonce = {1 : 2}
//	domain MessageID = {1 : 5}
//	domain UserID = {1 : 3}
//	domain PubKeyID = {1 : 3}
//	domain PrivKeyID = {1 : 3}
//	domain SessionNumbers = {0 : 1}
//	function maxProtocolRuns = 1 
	// These are bigger domains to demonstrate the feasibility  of the approach even in bigger cases
	domain Nonce = {1 : 10}
	domain MessageID = {1 : 16}
	domain UserID = {1 : 4}
	domain PubKeyID = {1 : 4}
	domain PrivKeyID = {1 : 4}
	// this avoid nonces being waisted in numerous protocol start without completion
	domain SessionNumbers = {0 : 2}
	function maxProtocolRuns = 2
	
	
	// STATIC FUNCTION
	// this inizialization is not elegant but is convenient for gerealization reason
	// these definitions work only cause of the implementation of all sets via integers
	// e.g. we use user1 = 1, pubKey1 = 1, privKey1 = 1
	function pubKeyFromPrivate($privK in PrivKeyID) = $privK
	function privKeyOf($u in UserID) = $u
	function pubKeyOf($u in UserID) = $u
	function ownerOfPrivKey($privK in PrivKeyID) = $privK
	function ownerOfPubKey($pubKey in PubKeyID) = $pubKey
	// only one spy
	function isSpy($u in UserID) = if $u = 1 then TRUE else FALSE endif
	
	
	
	// FUNCTION DEFINITIONS
	function isFresh($nonce in Nonce) = if not(exist $u in UserID with knowNonce($u,$nonce)=TRUE) then TRUE else FALSE endif
	
	function decryptNUK($m in MessageID, $k in PrivKeyID) =
		let ($message = messageNUK($m)) in
			if( isDef($message) ) then // another type of message may have arrived
				if( third($message) = pubKeyFromPrivate($k) ) then
					(first($message), second($message))
				endif
			endif
		endlet

	function decryptNNK($m in MessageID, $k in PrivKeyID) =
		let ($message = messageNNK($m)) in
			if( isDef($message) ) then // another type of message may have arrived
				if( third($message) = pubKeyFromPrivate($k) ) then
					(first($message), second($message))
				endif
			endif
		endlet

	function decryptNK($m in MessageID, $k in PrivKeyID) =
		let ($message = messageNK($m)) in
			if( isDef($message) ) then // another type of message may have arrived
				if( second(messageNK($m)) = pubKeyFromPrivate($k) ) then
					first($message)
				endif
			endif
		endlet
		
	
	
	
	// RULE DEFINITIONS

	rule r_send($s in UserID, $r in UserID, $m in MessageID) =
			par
				comunication($m) := ($s, $r)
				hasBeenRead($m)  := FALSE
			endpar
	
	rule r_sendNUK($sender in UserID) =
		par
			hasAlreadySent($sender) := TRUE
			startedSessions := startedSessions + 1
			choose $receiver in UserID with $receiver != $sender do
				choose $newNonce in Nonce with isFresh($newNonce) = TRUE do 
					par
						knowNonce($sender,$newNonce) := TRUE
						hasSentTo($sender,$newNonce) := $receiver
						isNonceArrivedToReceiver($newNonce) := FALSE
						choose $message in MessageID with messageType($message) = undef do 
							par
								messageType($message) := NUK
								messageNUK($message) := ($newNonce, $sender, pubKeyOf($receiver))
								r_send[$sender, $receiver, $message]
							endpar
					endpar
		endpar
	
	rule r_initSession($user in UserID) =
		if hasAlreadySent($user) = FALSE and startedSessions < maxProtocolRuns then
			choose $wantToSend in Bool with true do 
				if($wantToSend = TRUE) then
					r_sendNUK[$user]
				endif
		endif
		
	rule r_receiveNUK($receiver in UserID) =
		choose $m in MessageID with messageType($m) = NUK and hasBeenRead($m)=FALSE and second(comunication($m)) = $receiver do
			if first(comunication($m)) = $receiver then
				skip // ignore false communications (Users doesen't send messages to themselves)
			else
			let ($decrMessage = decryptNUK($m, privKeyOf($receiver))) in
				par
					hasBeenRead($m) := TRUE
					if $decrMessage = undef then 
						skip // Ignore. this happen when message is redirected or sent to receiver with a wrong pubKey
					else
						let($nonce0 = first($decrMessage), $exSender = second($decrMessage)) in
							if knowNonce($receiver,$nonce0) = TRUE then
								skip // ignore reply attack. User can see he already knew that nonce.
							else
								choose $newNonce in Nonce with isFresh($newNonce) = TRUE do
									par
										knowNonce($receiver,$nonce0) := TRUE
										knowNonce($receiver,$newNonce) := TRUE
										hasSentTo($receiver,$newNonce) := $exSender
										isNonceArrivedToReceiver($newNonce) := FALSE
										choose $response_message in MessageID with messageType($response_message) = undef do 
											par
												messageType($response_message) := NNK
												messageNNK($response_message) := ($nonce0, $newNonce, pubKeyOf($exSender))
												r_send[$receiver, $exSender, $response_message]
											endpar
									endpar
							endif
						endlet
					endif
				endpar
			endlet
			endif
			
	rule r_receiveNNK($receiver in UserID) =
		choose $m in MessageID with messageType($m) = NNK and hasBeenRead($m)=FALSE and second(comunication($m)) = $receiver do
			if first(comunication($m)) = $receiver then
				skip // ignore false communications (Users doesen't send messages to themselves)
			else
				let ($decrMessage = decryptNNK($m, privKeyOf($receiver))) in
					par
						hasBeenRead($m) := TRUE
						if $decrMessage = undef then // this happen when message is sent to receiver with a wrong pubKey
							skip
						else
							let($nonce1 = first($decrMessage), $nonce2 = second($decrMessage)) in
								if( knowNonce($receiver,$nonce1) = TRUE ) then  // check if he generated the received nonce
									par
										knowNonce($receiver,$nonce2) := TRUE
										isNonceArrivedToReceiver($nonce1) := TRUE
										let ($exReceiver = hasSentTo($receiver,$nonce1)) in // find the user who was initially sent nonce1
											choose $response_message in MessageID with messageType($response_message) = undef do 
												par
													messageType($response_message) := NK
													messageNK($response_message) := ($nonce2, pubKeyOf($exReceiver))
													r_send[$receiver, $exReceiver, $response_message]
												endpar
										endlet
									endpar
								endif
							endlet
						endif
					endpar
				endlet
			endif
	
	rule r_receiveNK($receiver in UserID) =
		choose $m in MessageID with messageType($m) = NK and hasBeenRead($m)=FALSE and second(comunication($m)) = $receiver do
			if first(comunication($m)) = $receiver then
				skip // ignore false communications (Users doesen't send messages to themselves)
			else
				let ($decrMessage = decryptNK($m, privKeyOf($receiver))) in
					par
						hasBeenRead($m) := TRUE
						if $decrMessage = undef then // this happen when message is sent to receiver with a wrong pubKey
							skip
						else
							let($nonce0 = $decrMessage) in
								if (knowNonce($receiver,$nonce0) = TRUE ) then
									// check if receiver already knew to have already established a correct connection
									// this discard the NK messages sent more times with the same nonce
									if(isNonceArrivedToReceiver($nonce0) = FALSE) then
										par
											isNonceArrivedToReceiver($nonce0) := TRUE
											terminatedSession := terminatedSession + 1
										endpar
									endif
								endif
							endlet
						endif
					endpar
				endlet
			endif
	
	rule r_behaveCorrectly($u in UserID) = 
		seq
			r_initSession[$u]
			r_receiveNUK[$u]
			r_receiveNNK[$u]
			r_receiveNK[$u]
		endseq
	
	
	rule r_receiveNUK_spy($receiver in UserID) = if isSpy($receiver) = TRUE then
		// Sometime behave honestly and sometime don't
		choose $behaveHonestly in Bool with true do
		if $behaveHonestly = TRUE then
			r_receiveNUK[$receiver]
		else
			// can read messages already read by others (e.g. he read and replayed)
			// can read messages that he is not the intended receiver
			choose $m in MessageID with messageType($m) = NUK do
				let ($decrMessage = decryptNUK($m, privKeyOf($receiver))) in
					// hasBeenRead($m) := TRUE // he doesen't change the message status because he is sneaky
					if $decrMessage = undef then // this happen when is not able to unencrypt the message
						// he CAN change the comunication's sender in someone different (this model any possibility, also the not useful)
//						choose $user in UserID with $user != $receiver do
//							let ($exSender = second($decrMessage)) in 
//								r_send[$user,$exSender,$m]
//							endlet
						// to check if this attack is effective we add the following invariant: each user shouldn't exchange more than one nonce with others
						skip
					else
						let($nonce0 = first($decrMessage), $exSender = second($decrMessage)) in 
							choose $newReceiver in UserID with $newReceiver != $receiver  do // can also send to the previous sender if omit "and $newReceiver != $exSender"
							par
								knowNonce($receiver,$nonce0) := TRUE // spy always save all the info it can 				
								hasSentTo($receiver,$nonce0) := $newReceiver // this is the reality and is true in any case
								// change message and send it again
								choose $modifyOldMessage in Bool with true do
									if $modifyOldMessage = TRUE then
										messageNUK($m) := ($nonce0, $receiver, pubKeyOf($newReceiver))
									else
										messageNUK($m) := ($nonce0, $exSender, pubKeyOf($newReceiver))
									endif
								choose $sendWithMyIdentity in Bool with true do
									if $sendWithMyIdentity = TRUE then
										r_send[$receiver, $newReceiver, $m]
									else
										par
											hasSentTo($exSender,$nonce0) := $newReceiver // this is what T will fake
											r_send[$exSender, $newReceiver, $m] // send old message
										endpar
									endif
							endpar
							
						endlet
					endif
				endlet
			endif
		endif
		
	rule r_receiveNK_spy($receiver in UserID) = if isSpy($receiver) = TRUE then
		// Sometime behave honestly and sometime don't
		choose $behaveHonestly in Bool with true do
		if $behaveHonestly = TRUE then
			r_receiveNK[$receiver]
		else
			// can read messages already read by others (e.g. he read and replayed)
			// can read messages that he is not the intended receiver
			choose $m in MessageID with messageType($m) = NK do
				let ($decrMessage = decryptNK($m, privKeyOf($receiver))) in
					// hasBeenRead($m) := TRUE // he doesen't change the message status because spy is sneaky
					if $decrMessage = undef then // this happen when message is sent to receiver with a wrong pubKey
						skip
					else
						let($nonce0 = $decrMessage) in
							par
								if (knowNonce($receiver,$nonce0) = FALSE ) then
									knowNonce($receiver,$nonce0) := TRUE // spy always save all the info it can 
								endif
								// instead of terminating the protocol he forward the content
								// terminatedSession := terminatedSession + 1
								let ($exSender= first(comunication($m))) in 
								choose $newReceiver in UserID with $newReceiver != $receiver do 
									par
										messageType($m) := NK
										messageNK($m) := ($nonce0, pubKeyOf($newReceiver))
										choose $doSendAsSpy in Bool with true do
											if $doSendAsSpy = TRUE then
												r_send[$receiver, $newReceiver, $m]
											else
												r_send[$exSender, $newReceiver, $m]
											endif
									endpar
								endlet
							endpar
						endlet
					endif
				endlet
		endif endif
	
	rule r_behaveRandomly($u in UserID) = if isSpy($u) = TRUE then
		seq
			// r_initSession[$u]
			r_receiveNUK_spy[$u]
			// r_receiveNNK_spy[$u]
			r_receiveNK_spy[$u]
		endseq	
	endif
	
//	rule r_simulatedMain = 
//		choose $u in UserID with true do
//			if isSpy($u) = TRUE then
//				r_behaveRandomly[$u] // r_behaveCorrectly[$u] // 
//			else
//				r_behaveCorrectly[$u]
//			endif
			

	
	
// INITIAL STATE
//default init s0:
//	function startedSessions = 0
//	function terminatedSession = 0
//	function hasAlreadySent($u in UserID) = FALSE
//	function knowNonce($u in UserID, $n in Nonce) = FALSE
//	function isNonceArrivedToReceiver($n in Nonce) = FALSE
//	
//	function comunication($m in MessageID) = (undef, undef) 
//	function messageType($m in MessageID) = undef
	
