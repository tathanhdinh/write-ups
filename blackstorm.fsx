let reg_question = "30 31 31 31 31 30 30 30 20 30 31 30 31 31 31 31 30 20 30 30 31 31 30 30 31 30 20 30 30 31 30 30 30 30 30 20 30 30 31 30 31 31 30 31 20 30 30 31 30 30 30 30 30 20 30 30 31 31 31 30 30 30 20 30 31 31 31 31 30 30 30 20 30 30 31 30 30 30 30 30 20 30 30 31 30 31 30 31 31 20 30 30 31 30 30 30 30 30 20 30 30 31 31 30 30 30 31 20 30 30 31 31 30 31 31 30 20 30 30 31 30 30 30 30 30 20 30 30 31 31 31 31 30 31 20 30 30 31 30 30 30 30 30 20 30 30 31 31 30 30 30 30 20 30 30 31 30 31 31 30 30 20 30 30 31 30 30 30 30 30 20 30 31 30 30 30 31 30 31 20 30 31 31 30 31 31 31 30 20 30 31 31 31 30 31 30 30 20 30 31 31 30 30 31 30 31 20 30 31 31 31 30 30 31 30 20 30 30 31 30 30 30 30 30 20 30 30 31 30 31 30 30 30 20 30 31 31 31 31 30 30 30 20 30 30 31 30 30 30 30 30 20 30 30 31 30 31 30 31 30 20 30 30 31 30 30 30 30 30 20 30 30 31 31 30 30 31 31 20 30 30 31 31 30 31 30 31 20 30 30 31 31 30 30 30 30 20 30 30 31 30 31 30 30 31"

let decode_question (question:string) =
  let hex_str_array = Array.map (fun str -> "0x" + str) <| question.Split [|' '|]
  let int_val_array = Array.map (fun str -> int32 str) hex_str_array
  let char_val_array = Array.map (fun i -> char i) int_val_array
  let binary_str = System.String char_val_array
  let binary_str_array = binary_str.Split [|' '|]
  let binary_val_array = Array.map (fun str -> System.Convert.ToUInt32(str, 2)) binary_str_array
  let converted_char_array = Array.map (fun i -> char i) binary_val_array
  let converted_str = System.String converted_char_array
  converted_str

let fast_decode (text:string) =
  let binary_text =
    text.Split [|' '|]
    |> Array.map (fun str -> "0x" + str)
    |> Array.map (fun str -> uint32 str)
    |> Array.map (fun i -> char i)
    |> System.String
  binary_text.Split [|' '|]
  |> Array.map (fun str -> System.Convert.ToUInt32(str, 2))
  |> Array.map (fun i -> char i)
  |> System.String

let faster_decode (text:string) =
  let binary_text =
    text.Split [|' '|] |> Array.map (fun str -> "0x" + str |> uint32 |> char) |> System.String
  binary_text.Split [|' '|] |> Array.map (fun str -> System.Convert.ToUInt32(str, 2) |> char) |> System.String

let even_faster_decode (text:string) =
  (text.Split [|' '|]
   |> Array.map (fun str -> "0x" + str |> uint32 |> char)
   |> System.String).Split [|' '|]
  |> Array.map (fun str -> System.Convert.ToUInt32(str, 2) |> char)
  |> System.String

decode_question reg_question
fast_decode reg_question
