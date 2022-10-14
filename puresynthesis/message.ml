module Message = struct
  type t = {depth: int; show: bool}

  let create (show:bool): t = {depth = 1; show}

  let depth (m:t) : int = m.depth

  let incr_depth (m:t) : t = {depth = m.depth+1; show=m.show}

  let decr_depth (m:t) : t = {depth = m.depth-1; show = m.show}

  let show (m:t) (s:string) = if m.depth <= 0 || not m.show then Printf.printf "NOICE" else Printf.printf "%s" ("\n"^ (String.make m.depth ' ') ^s)

  let show_with_newlines (m:t) (s:string) = (String.split_on_char '\n' s) |> List.iter (show m)
end