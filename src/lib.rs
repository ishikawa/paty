peg::parser! {
    pub grammar parser() for str {
        rule _() = quiet!{[' ' | '\n' | '\t']*}
        rule number() -> u32
          = _ n:$(['0'..='9']+) _ {? n.parse().or(Err("u32")) }

        pub rule list() -> Vec<u32>
          = "[" l:number() ** "," "]" { l }
    }
}
