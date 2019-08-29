module Frinf
open FSharp.Data
open FSharp.Data.JsonExtensions
open System.IO
open System
open Newtonsoft.Json.Linq
open Newtonsoft.Json
open System.Reflection
open System.Collections.Generic

module StringDistance =
    type WagnerFischerLazyResult =
        { matches : string
          wflparameter : int }

    type Comparison(source : seq<string>, limit : int, target : string) =

        let wagnerFischerLazy (wflsource : string) (wfldest : string) =
            let inline min3 one two three =
                if one < two && one < three then one
                elif two < three then two
                else three

            let sourceLength = wflsource.Length
            let destLength = wfldest.Length
            let d = Array2D.create (sourceLength + 1) (destLength + 1) -1

            let rec dist =
                function
                | i, 0 -> i
                | 0, j -> j
                | i, j when d.[i, j] <> -1 -> d.[i, j]
                | i, j ->
                    let dval =
                        if wflsource.[i - 1] = wfldest.[j - 1] then
                            dist (i - 1, j - 1)
                        else
                            min3 (dist (i - 1, j) + 1) (dist (i, j - 1) + 1)
                                (dist (i - 1, j - 1) + 1)
                    d.[i, j] <- dval
                    dval
            dist (sourceLength, destLength)

        member this.Wfl() =
            source
            |> Seq.map (fun name ->
                   { matches = name
                     wflparameter = wagnerFischerLazy name target })
            |> Seq.sortBy (fun result -> result.wflparameter)
            |> Seq.take limit
            |> Seq.map (fun result -> result.matches)

        member this.SString() =
            source
            |> Seq.choose (fun unit ->
                   if unit.Contains(target) then Some unit
                   else None)

        member this.All() = this.Wfl() |> Seq.append (this.SString())


module FrinfEvaluator =
    type UnitType =
        | Unit of string * int 
        | CompositeUnit of UnitType list     
        static member Create(s) = Unit(s,1)
        static member Dimensionless() = Unit("",0)
        override this.ToString() =
            let exponent = function
                | Unit(_,n) -> n
                | CompositeUnit(_) ->                
                    raise (new System.InvalidOperationException())
            let rec toString = function        
                | Unit(s,n) when n=0 -> ""
                | Unit(s,n) when n=1 -> s
                | Unit(s,n)          -> s + " ^ " + n.ToString()            
                | CompositeUnit(us) ->               
                    let ps, ns = 
                        us |> List.partition (fun u -> exponent u >= 0)
                    let join xs = 
                        let s = xs |> List.map toString |> List.toArray             
                        System.String.Join(" ",s)
                    match ps,ns with 
                    | ps, [] -> join ps
                    | ps, ns ->
                        let ns = ns |> List.map UnitType.Reciprocal
                        join ps + " / " + join ns
            match this with
            | Unit(_,n) when n < 0 -> " / " + toString this
            | _ -> toString this    
        static member ( * ) (v:ValueType,u:UnitType) = UnitValue(v,u) 
        static member ( * ) (u:UnitType, v:ValueType) = UnitValue(v,u)
        static member ( * ) (lhs:UnitType,rhs:UnitType) =
            let text = function
                | Unit(s,n) -> s
                | CompositeUnit(us) -> us.ToString()
            let normalize us u =
                let t = text u
                match us |> List.tryFind (fun x -> text x = t), u with
                | Some(Unit(s,n) as v), Unit(_,n') ->
                    us |> List.map (fun x -> if x = v then Unit(s,n+n') else x)                 
                | Some(_), _ -> raise (new System.NotImplementedException())
                | None, _ -> us@[u]
            let normalize' us us' =
                us' |> List.fold (fun (acc) x -> normalize acc x) us
            match lhs,rhs with
            | Unit(u1,p1), Unit(u2,p2) when u1 = u2 ->
                Unit(u1,p1+p2)        
            | Unit(u1,p1), Unit(u2,p2) ->            
                CompositeUnit([lhs;rhs])
            | CompositeUnit(us), Unit(_,_) ->
                CompositeUnit(normalize us rhs)
            | Unit(_,_), CompositeUnit(us) ->
                CompositeUnit(normalize' [lhs]  us)
            | CompositeUnit(us), CompositeUnit(us') ->
                CompositeUnit(normalize' us us')
            | _,_ -> raise (new System.NotImplementedException())
        static member Reciprocal x =
            let rec reciprocal = function
                | Unit(s,n) -> Unit(s,-n)
                | CompositeUnit(us) -> CompositeUnit(us |> List.map reciprocal)
            reciprocal x
        static member ( / ) (lhs:UnitType,rhs:UnitType) =        
            lhs * (UnitType.Reciprocal rhs)
        static member ( + ) (lhs:UnitType,rhs:UnitType) =       
            if lhs = rhs then lhs                
            else raise (new System.InvalidOperationException())
    and ValueType = float32
    and UnitValue(v:ValueType,u:UnitType) = 
        member this.Value = v 
        member this.Unit = u
        override this.ToString() = sprintf "%O %O" v u
        static member (+) (lhs:UnitValue,rhs:UnitValue) =
            UnitValue(lhs.Value+rhs.Value, lhs.Unit+rhs.Unit)
            // cn added:
        static member (*) (lhs:float32,rhs:UnitValue) =                    
            UnitValue(lhs*rhs.Value,rhs.Unit)                
        static member (*) (lhs:UnitValue,rhs:UnitValue) =                    
            UnitValue(lhs.Value*rhs.Value,lhs.Unit*rhs.Unit)                
        static member (*) (lhs:UnitValue,rhs:ValueType) =        
            UnitValue(lhs.Value*rhs,lhs.Unit)      
        static member (*) (v:UnitValue,u:UnitType) = 
            UnitValue(v.Value,v.Unit*u)  
        static member (/) (lhs:UnitValue,rhs:UnitValue) =                    
            UnitValue(lhs.Value/rhs.Value,lhs.Unit/rhs.Unit)
        static member (/) (lhs:UnitValue,rhs:ValueType) =
            UnitValue(lhs.Value/rhs,lhs.Unit)  
        static member (/) (v:UnitValue,u:UnitType) = 
            UnitValue(v.Value,v.Unit/u)
    type UnitFormat =
        { unitName : string
          unitValue : int }
    type UnitSymbol =
        { K : int
          S : int
          Bit : int
          Dollar : int
          Cd : int
          Kg : int
          A : int
          m : int
          mol : int }
    type Units =
        | K
        | S
        | Bit
        | Dollar
        | Cd
        | Kg
        | A
        | M
        | Mol
    type UnitAndValue =
        { v : string
          u : UnitSymbol }
        member this.ToUnitType() =
        
            let valueAsFloat : float32 = System.Single.Parse(this.v)

            let unitSymbolMap (u : UnitSymbol) =
                Map.ofList ([ (K, u.K)
                              (S, u.S)
                              (Bit, u.Bit)
                              (Dollar, u.Dollar)
                              (Cd, u.Cd)
                              (Kg, u.Kg)
                              (A, u.A)
                              (M, u.m)
                              (Mol, u.mol) ])
                |> Map.filter (fun _ v -> v <> 0)

            let generateUnit =
                unitSymbolMap this.u
                |> Map.map
                       (fun k v ->
                       let theUnit = UnitType.Create(k.ToString())

                       let action =
                           if v > 0 then (*)
                           else (/)

                       let state =
                           if v > 0 then id
                           else UnitType.Reciprocal

                       Seq.replicate ((Math.Abs v) - 1)
                           (UnitType.Create(k.ToString()))
                       |> Seq.fold action (state theUnit))
                |> Map.toSeq
                |> Seq.map (snd)
                |> Seq.reduce (*)

            valueAsFloat * generateUnit

        member this.ToDimensionLess() =
            let valueAsFloat : float32 = System.Single.Parse(this.v)       
            valueAsFloat * UnitType.Dimensionless()
   
    let items =
        let source =
            JsonValue.Load
                (__SOURCE_DIRECTORY__ + "/resources/units.json")


        let retrieveProperty prop =
            match source.TryGetProperty(prop) with
            | Some(u) -> u
            | None -> JsonValue.Array [||]

        let units = retrieveProperty "units"
        let prefixes = retrieveProperty "prefixes"
        let standalonePrefixes = retrieveProperty "standalone-prefixes"
    
        Array.concat [ units.Properties
                           |> Array.map (fun (a, b) ->
                                  (a,
                                   let v = JObject.Parse(b.ToString())
                                   let unitAndValue =
                                       JsonConvert.DeserializeObject<UnitAndValue>
                                           (v.ToString())
                                   try
                                       unitAndValue.ToUnitType()
                                   with _ -> 1.0f * UnitType.Create("K")));
                           prefixes.Properties
                           |> Array.map (fun (a, b) ->
                                  (a,
                                   let v = JObject.Parse(b.ToString())
                                   let unitAndValue =
                                       JsonConvert.DeserializeObject<UnitAndValue>(v.ToString())
                                   unitAndValue.ToDimensionLess()
                                   ));
                            standalonePrefixes.Properties
                           |> Array.map (fun (a, b) ->
                                  (a,
                                   let v = JObject.Parse(b.ToString())
                                   let unitAndValue =
                                       JsonConvert.DeserializeObject<UnitAndValue>(v.ToString())
                                   unitAndValue.ToDimensionLess()
                                   ))
                              ]
        |> dict

    let (|Number|_|) (input : string) = try
                                           let result = System.Single.Parse(input)
                                           Some(result)
                                        with
                                            | _ -> None
    let (|Unit|_|) (input: string) = if input.Length>0 then Some(input.Trim()) else None
    let eval (input : string) =
        let pieces n =
            let x = input.Split(':') |> Array.map (fun s -> s.Trim())
            x.[n].Split(' ') |> List.ofArray
        let (tokensL, tokensR) = (pieces 0, pieces 1)
        let rec go input res =
            match input with
            | [] -> res
            | a :: b ->
                match a with
                | Number n -> go b (n :: (fst res), snd res)
                | Unit u -> go b (fst res, items.[u] :: (snd res))
                | _ -> go b res
    
        let rlhs tokens =
            match go tokens ([], []) with
            | ([], x :: xs) -> Seq.reduce (*) (x :: xs)
            | (a, b) -> Seq.reduce (*) a * Seq.reduce (*) b
    
        let (_, _d) = go tokensR ([], [])
        rlhs tokensL / rlhs tokensR
    
    let matches (input : string) =
        let sortAndChop =
            Set.ofSeq
            >> Set.toSeq
            >> Seq.sortBy (fun (x : string) -> x.Length)
    
        let searcher = new StringDistance.Comparison(items.Keys, 4, input)
        let results = searcher.All()
        if Seq.length results > 16 then Seq.take 16 results |> sortAndChop
        else results |> sortAndChop

[<EntryPoint>]
let main argv =
    printfn "%s" "Frink F#, version 0.0.1: Units of measure calculator\n\nFor help type ? to search keys use 'find'\nLoading and parsing json source ... done.\n"
    let samples = ["51 grams TNT : 185 pounds gravity feet"; "10 feet 12 feet 8 feet : gallons";
                   "2 fathoms water gravity barrel : 40 watts minutes"; "51 grams TNT : teaspoons gasoline" ] 

    let getSampleEntry() = 
        let idx = new System.Random()
        samples.[idx.Next(samples.Length)]

    let (|Lookup|_|) (input:string) =
        if input.StartsWith("find")
        then Some(input.Split(' ') 
            |> Array.skip 1 |> Array.fold (+) ""
            |> FrinfEvaluator.matches)
        else None

    let repl =
        while true do
            printf "%s"  "Frinf#> "
//            let rec keyloop (entry: char list) = 
//                let y = Console.ReadKey()
//                match y.Key with
//                | ConsoleKey.Tab -> entry
//                                        |> Array.ofList
//                                        |> Array.rev
//                                        |> String
//                                        |> FrinfEvaluator.matches
//                                        |> Seq.iter (printfn "%s" )
//                                    keyloop entry
//                | ConsoleKey.Enter -> entry
//                | _ -> keyloop (y.KeyChar :: entry)
//            
//            let results1 = keyloop []
//            printfn "Result of first loop:%s" (results1 |> Array.ofList |> String)

            let input = System.Console.ReadLine()
            match input with
            | Lookup results -> results |> Seq.iter (printfn "%s")
            | "?" -> let sample = getSampleEntry()
                     printfn "Example: %s, result: %s" sample ((FrinfEvaluator.eval sample).ToString())
            | _ ->   printfn "Result: %s" ((FrinfEvaluator.eval input).ToString())
    repl
    0
