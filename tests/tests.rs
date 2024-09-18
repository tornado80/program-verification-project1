use datatest_stable::Utf8Path;
use itertools::Itertools;
use regex::Regex;
use slang_template::App;
use slang_ui::prelude::slang::Position;
use std::collections::HashSet;

datatest_stable::harness!(test_verifier, "tests", r"(.*).\.slang");
fn test_verifier(_path: &Utf8Path, content: String) -> datatest_stable::Result<()> {
    let actual = slang_ui::test(App, &content)
        .reports()
        .iter()
        .map(|x| Position::from_byte_offset(&content, x.span.start()).line + 1)
        .unique()
        .sorted()
        .collect::<HashSet<_>>();
    let re = Regex::new(r"\s*//\s+(@CheckError)").unwrap();
    let expected = re
        .find_iter(&content)
        .map(|c| Position::from_byte_offset(&content, c.start() + 2).line + 2)
        .unique()
        .sorted()
        .collect::<HashSet<_>>();
    let extra_errors = actual.difference(&expected).collect::<HashSet<_>>();
    let missing_errors = expected.difference(&actual).collect::<HashSet<_>>();

    if !extra_errors.is_empty() && !missing_errors.is_empty() {
        Err(format!(
            "Extra errors in lines: {}. Missing errors in lines: {}.",
            extra_errors.iter().join(", "),
            missing_errors.iter().join(", ")
        )
        .into())
    } else if extra_errors.is_empty() && !missing_errors.is_empty() {
        Err(format!(
            "Missing errors in lines: {}.",
            missing_errors.iter().join(", ")
        )
        .into())
    } else if !extra_errors.is_empty() && missing_errors.is_empty() {
        Err(format!("Extra errors in lines: {}.", extra_errors.iter().join(", ")).into())
    } else {
        Ok(())
    }
}
