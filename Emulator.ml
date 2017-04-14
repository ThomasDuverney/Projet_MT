(* Micha�l P�RIN, Verimag / Universit� Grenoble-Alpes, F�vrier 2017
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * (PROJECT 2019)  1. Multi-Bands Turing Machines working on a an alphabet A can be simulated by a single band Turing Machine using a augmented Alphbet A'
 *
 * (PROJECT 2017)  2. A Turing Machine using an alphabet A can be simulated by a Turing Machine using the binary alphabet {B,D}
 *
 * This module provides means to write Emulator for Problems 1 and 2.
 *
*)



open Tricks
open State
open Action
open Transition
open Band
open Configuration
open Turing_Machine
open Execution



type emulator   = State.t * Action.t * State.t -> Turing_Machine.t
type translator = Band.t list -> Band.t list

type simulator  =
  { name: string ;
    encoder: translator ;
    decoder: translator ;
    emulator: emulator
  }

type simulators = simulator list


module Simulator =
  (struct

    type loggers = Logger.t list

    let (fake_tm_named: string ->  Turing_Machine.t) = fun name ->
      Turing_Machine.finalize name Turing_Machine.nop

    let (show_bands_using: loggers -> string -> Band.t list -> Band.t list) = fun loggers name bands ->
      begin
        (Configuration.make (fake_tm_named name) bands) >> (Configuration.print_using loggers) ;
        bands
      end

    let rec (execute_action_using: simulators * loggers -> (State.t * Action.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (src,action,tgt) cfg ->
      let cfg = cfg >> (Configuration.show_using loggers)
      in
      let next_bands =
        match simulators with
        | [] -> Action.perform action cfg.bands

        | simulator :: other_simulators
          ->
          let e_tm    = simulator.emulator (src,action,tgt)
          and e_bands = (simulator.encoder  cfg.bands) >> (show_bands_using loggers (String.concat " to " [ "encoding" ; simulator.name ]))
          in let e_cfg = Configuration.make e_tm e_bands
          in
          let e_next_cfg = log_run_using (other_simulators,loggers) e_cfg
          in
          let bands_updated_by_emulation = (simulator.decoder e_next_cfg.bands) >> (show_bands_using loggers (String.concat " " [ simulator.name ; "decoding"]))
          in
          let bands_updated_by_execution = Action.perform action cfg.bands
          in
          if (* FIXME: Band.are_equivalents *) bands_updated_by_execution = bands_updated_by_emulation
          then bands_updated_by_execution
          else failwith
              (String.concat "\n" [ "execute_action_using: simulation errors" ;
                                    Band.to_ascii_many bands_updated_by_emulation ;
                                    "are not equivalent to" ;
                                    Band.to_ascii_many bands_updated_by_execution ;
                                  ])
      in
      { cfg with bands = next_bands }


    and (execute_single_band_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Band.t -> Band.t) = fun (simulators,loggers) (src,instruction,tgt) band ->
      let cfg = Configuration.make (fake_tm_named (Instruction.pretty instruction)) [band]
      in let next_cfg = execute_instruction_using (simulators,loggers) (src,instruction,tgt) cfg
      in List.hd next_cfg.bands

    and (execute_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
      (match instruction with
       | Run tm -> (* FIXME: ajoutez les transitions (source -nop-> init) et (accept -nop-> target) *)
         run_using (simulators,loggers) (Configuration.make tm cfg.bands)

       | Seq [] -> cfg
       | Seq (inst::instructions) ->
         let intermediate_state = State.fresh_from source in
         cfg
         >> (execute_instruction_using (simulators,loggers) (source, inst, intermediate_state))
         >> (execute_instruction_using (simulators,loggers) (intermediate_state, Seq instructions, target))

       | Parallel instructions ->
         let next_bands =
           List.map
             (fun (inst,band) -> execute_single_band_instruction_using (simulators,loggers) (source,inst,target) band)
             (Instruction.zip instructions cfg.bands)
         in { cfg with bands = next_bands }

       | Action action -> execute_action_using (simulators,loggers) (source,action,target) cfg
      )

    and (execute_transition_using: simulators * loggers -> Transition.t -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
      let next_cfg = execute_instruction_using (simulators,loggers) (source,instruction,target) cfg
      in { next_cfg with state = target}

    and (run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
      match Execution.select_enabled_transition cfg.tm cfg with
      | None -> cfg
      | Some transition ->
        let next_cfg = execute_transition_using (simulators,loggers) transition cfg
        in run_using (simulators,loggers) next_cfg

    and (log_run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
      let loggers = cfg.logger :: loggers
      in
      let final_cfg = (run_using (simulators,loggers) cfg) >> (Configuration.show_using loggers)
      in
      begin
        cfg.logger#close ;
        final_cfg
      end

  end)


open State
open Symbol
open Alphabet
open Pattern
open Action
open Band
open Transition
open Turing_Machine
open MyList
open Bit_Vector
(* An example of a useless but correct translation that splits the effect of a transition into three steps

   (q) -- l / e : d --> (q')
   ===
   (q) -- l : H --> (q.0) -- ANY / e : H --> (q.00) -- ANY : d --> (q')
*)


module Split =
  (struct

    (* TRANSLATION OF BANDS *)

    let (encode: translator) = fun x -> x

    (* REVERSE TRANSLATION *)

    let (decode: translator) = fun x -> x

    (* EMULATION OF TRANSITIONS *)

    let (just_read: reading -> Action.t) = fun reading ->
      RWM (reading, No_Write, Here)

    let (just_write: writing -> Action.t) = fun writing ->
      match writing with
      | No_Write     -> Nop
      | Write symbol -> RWM (Match(ANY), Write symbol, Here)

    let (just_move: moving -> Action.t) = fun moving ->
      RWM (Match(ANY), No_Write, moving)

    let (synchronize: Action.t list -> Instruction.t) = fun actionS ->
      let rec (rec_synchronize: ('r list * 'w list * 'm list) -> Action.t list -> ('r list * 'w list * 'm list)) = fun (reads,writes,moves) actions ->
        match actions with
        | [] -> (List.rev reads, List.rev writes, List.rev moves)
        | action::actions ->
          (match action with
           | Nop        -> rec_synchronize ( Nop::reads , Nop::writes , Nop::moves) actions
           | RWM(r,w,m) -> rec_synchronize ( (just_read r)::reads , (just_write w)::writes , (just_move m)::moves) actions
           | Simultaneous _ -> failwith "Emulator.Split.synchronize: nested Simultaneous"
          )
      in
      let (reads,writes,moves) = rec_synchronize ([],[],[]) actionS
      in
      Seq[ Action(Simultaneous(reads)) ; Action(Simultaneous(writes)) ; Action(Simultaneous(moves)) ]

    let rec (transitions_emulating: State.t * Action.t * State.t -> Transition.t list) = fun (source,action,target) ->
      (match action with
       | Nop -> [ (source, Action(Nop), target) ]

       | RWM(r,w,m) -> [ (source, Seq[ Action(just_read r) ; Action(just_write w) ; Action(just_move m) ], target) ]

       | Simultaneous actions -> [ (source, synchronize actions, target) ]
      )

    and (emulate_action: emulator) = fun (source,action,target) ->
      let (source,target) =
        if source <> target   (* /!\ loop in the emulated TM if source-target *)
        then (source,target)
        else (State.initial, State.accept)
      in
      let transitions =  transitions_emulating (source,action,target) in
      { Turing_Machine.nop with
        name = String.concat "" [ "Split" ; Pretty.parentheses (Transition.to_ascii (source,Action action, target)) ] ;
        initial = source ;
        accept  = target ;
        transitions = transitions
      }

    (* THE SIMULATOR *)

    let (* USER *) (simulator: simulator) = { name = "Split" ; encoder = encode ;  decoder = decode ; emulator = emulate_action }

  end)




module Binary =
struct

  (* TRANSLATION OF BANDS *)

  (* The modules Bit and Bits are defined in Alphabet.ml *)

  (** NEW 27/03/2107 *)
  type encoding = (Symbol.t * Bits.t) list

  let rec map_on_bits : Bits.t -> (Bit.t -> Symbol.t) -> Symbol.t list = fun bits f ->
  match bits with
  |[] -> print_endline "" ; []
  |h::t -> print_string ((Symbol.pretty h) ^ " ") ; (f h) :: map_on t f ;;


  (** NEW 27/03/2107 *)
  (*Fonction renvoie la taille d'une liste. Utile pour la suite avec la fonction enumerate*)
  let length : 'a list -> int = fun l -> List.fold_left (fun acc e -> succ acc) 0 l ;;
  (* Fonction qui prend un symbole
  let symbol_to_bits : Symbol.t -> Bits.t =*)

  (* Parcours* l'aphabet et associe un vecteur de bit à chaque symbols grâce à la fonction symbol_to_bits *)
  let build_encoding : Alphabet.t -> encoding =
  let bit_as_boolean_to_bit : Bit_as_Boolean.t -> Bit.t =
  fun bit -> match Bit_as_Boolean.pretty bit with
  "0" -> Bit.zero | "1" -> Bit.unit in

  fun alphabet -> zip alphabet.symbols (map_on (BV.enumerate (List.length alphabet.symbols))
  (fun vec_bit -> map_on vec_bit bit_as_boolean_to_bit)) ;;

  (** MODIFIED 27/03/2107 *)
  let encode_with : encoding -> Band.t list -> Band.t list
    = fun encoding ->
      fun bands ->

      let bit_to_symbol : Bit.t -> Symbol.t = fun bit -> match bit with zero -> B | unit -> D in
      map_on bands (fun band -> { empty with

          left = map_on band.left (fun symbol -> Vector (map_on_bits (List.assoc symbol encoding) bit_to_symbol)) ;
          head = Vector (map_on_bits (List.assoc band.head encoding) bit_to_symbol) ;
          right = map_on band.right (fun symbol -> Vector (map_on_bits (List.assoc symbol encoding) bit_to_symbol)) ;
          alphabet = { symbols = [B;D]; symbol_size_in_bits = band.alphabet.symbol_size_in_bits}
      });;


  (* REVERSE TRANSLATION *)

  (** MODIFIED 27/03/2107 *)
  let decode_with : encoding -> Band.t list -> Band.t list
  (* PROJET 2017: modifiez ce code -> *)
    = fun encoding ->
    fun bands -> map_on bands (fun band -> { empty with

        left =  band.left ;
        head = band.head(*A COMPLETER*);
        right = band.right(*A COMPLETER*);
        alphabet = band.alphabet(*A COMPLETER*);
    });;

    (*  let decode_with : encoding -> Band.t list -> Band.t list
           let vector_to_bits : Symbol.t -> Bits.t = fun vec_sym -> let Vector bits = vec_sym in bits in
        = fun encoding ->
        fun bands ->
         map_on bands (fun band -> { empty with

            left =  map_on band.left vector_to_bits ;
            head = band.head;
            right = band.right;
            alphabet = band.alphabet;
        });;*)

    let build_encoding : Alphabet.t -> encoding =
    let bit_as_boolean_to_bit : Bit_as_Boolean.t -> Bit.t =
    fun bit -> match Bit_as_Boolean.pretty bit with
    "0" -> Bit.zero | "1" -> Bit.unit in

    fun alphabet -> zip alphabet.symbols (map_on (BV.enumerate (List.length alphabet.symbols))
    (fun vec_bit -> map_on vec_bit bit_as_boolean_to_bit)) ;;


  (* EMULATION OF TRANSITIONS *)

  let (emulate_action: State.t * Action.t * State.t -> Turing_Machine.t)
  (* PROJET 2017: modifiez ce code -> *)
    = fun (source,action,target) ->
      { Turing_Machine.nop with
        name = String.concat "" [ "Binary" ; Pretty.parentheses (Action.to_ascii action) ] ;
        initial = State.initial ;
        accept  = State.accept ;
        transitions = [(State.initial,Action(action),State.accept)]
      }

  (* THE SIMULATOR *)

  (** MODIFIED 27/03/2107 *)
  let make_simulator : Alphabet.t -> simulator
    = fun alphabet ->
      let encoding = build_encoding alphabet in
      { name = "Binary" ;
        encoder = encode_with encoding ;
        decoder = decode_with encoding ;
        emulator = emulate_action
      }

end


(* DEMO *)

open Alphabet

(* let _final_cfg = Simulator.log_run_using in *)

let (demo: unit -> Band.t list) = fun () ->
  let alphabet = Alphabet.make [B;Z;U] in
  let band = Band.make alphabet [U;U;Z;U] in
  let tm = Turing_Machine.incr in
  let cfg = Configuration.make tm [ band ] in
  let sim = Binary.make_simulator alphabet in
  sim.encoder cfg.bands ;;

     (*) ([ (* Split.simulator ; *)
        (** MODIFIED 27/03/2107 *) Binary.make_simulator alphabet
      ],[])
      cfg
  in ()*)
