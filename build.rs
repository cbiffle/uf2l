use std::io::Write;
use serde::Deserialize;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Load UF2 family JSON.
    println!("cargo:rerun-if-changed=uf2families.json");
    let json_families = std::fs::read_to_string("uf2families.json")?;
    // Parse it, so we don't have to parse it at runtime.
    let mut families: Vec<FamilyRecord> = serde_json::from_str(&json_families)?;

    // Generate Rust literals describing the family data. We'll produce it
    // sorted by name so we can binary search, which is premature optimization
    // but whatever.
    families.sort_by_key(|f| f.short_name.clone());

    let out_dir = std::env::var("OUT_DIR")?;
    let out_dir = std::path::Path::new(&out_dir);
    let out_path = out_dir.join("uf2families.rs");

    let mut out = std::fs::File::create(out_path)?;

    writeln!(out, "static FAMILIES: &[(u32, &str, &str)] = &[")?;
    for f in families {
        let id = if f.id.starts_with("0x") {
            u32::from_str_radix(&f.id[2..], 16)?
        } else {
            f.id.parse()?
        };
        writeln!(out, "    ({:#x}, {:?}, {:?}),",
            id,
            f.short_name,
            f.description)?;
    }
    writeln!(out, "];")?;

    Ok(())
}

#[derive(Deserialize)]
struct FamilyRecord {
    id: String,
    short_name: String,
    description: String,
}
