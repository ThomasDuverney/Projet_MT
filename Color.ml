(* Michaël PÉRIN, Verimag / Université Grenoble-Alpes, Février 2017 
 *
 * - library of predefined colors and color format conversion
 *
 *)

(* REQUIRES 
     graphics.cma pretty.cmo
   COMPILATION 
     ocamlc graphics.cma color.ml
*)
  
type color = 
  | RGB of Graphics.color (* Graphics.color is a integer == r * 256^2 + g * 256 + b *)
  | COL of string
	
type t = color

let (orange:color)  = RGB (Graphics.rgb 229 83 0)
let (indigo:color)  = RGB (Graphics.rgb 75 0 130)
let (black:color)   = COL "black"
let (white:color)   = COL "white"
let (magenta:color) = COL "magenta"
let (cyan:color)    = COL "cyan"
let (blue:color)    = COL "blue"
let (yellow:color)  = COL "yellow"
let (red:color)     = COL "red"
let (gray:color)   = COL "gray"
let (green:color)   = COL "green"    
      
let (default:color) = black
  
let rec (random_color: unit -> color) = fun () ->
      let r = Random.int 255 
      and g = Random.int 255 
      and b = Random.int 255 
      in let c = Graphics.rgb r g b 
      in if c = Graphics.white then random_color () else RGB c

let (int_to_rgb: int -> int * int * int) = fun c ->
      let r = c / 65536 and g = (c / 256) mod 256 and b = c mod 256 
      in (r,g,b)
	
let (color_to_rgb: color -> int * int * int) = fun color ->
      match color with
      | RGB c -> int_to_rgb c
      | COL "white"   -> int_to_rgb Graphics.white
      | COL "black"   -> int_to_rgb Graphics.white
      |	COL "magenta" -> int_to_rgb Graphics.magenta
      | COL "cyan"    -> int_to_rgb Graphics.cyan
      | COL "blue"    -> int_to_rgb Graphics.blue
      | COL "yellow"  -> int_to_rgb Graphics.yellow
      | COL "red"     -> int_to_rgb Graphics.red
		
let (inv_rgb_color: color -> color) = fun color ->
      let (r,g,b) = color_to_rgb color 
      in RGB (Graphics.rgb (255-r) (255-g) (255-b))
    

let (rgb_to_string: color -> string) = fun color ->
   let (r,g,b) = color_to_rgb color
   in  String.concat "" (List.map (Pretty.Type.filled_integer 255) [r;g;b])

	  
let (color_to_html: color -> string) = fun color ->
      match color with
      | RGB c -> "#" ^ (string_of_int c)
      | COL name -> name
