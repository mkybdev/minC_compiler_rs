#[macro_export]
/// Concatenates the given expressions with trailing line breaks.
macro_rules! cogen_concat {
    ($($e:expr),*) => {
        {
            let mut s = String::new();
            $(
                s.push_str(&$e);
                s.push_str("\n");
            )*
            s.strip_suffix("\n").unwrap().to_string()
        }
    };
}

#[macro_export]
/// Concatenates the given expressions with leading tabs and trailing line breaks.
macro_rules! cogen_concat_tab {
    ($($e:expr),*) => {
        {
            let mut s = String::new();
            $(
                s.push_str("\t");
                s.push_str(&$e);
                s.push_str("\n");
            )*
            s.strip_suffix("\n").unwrap().to_string()
        }
    };
}
