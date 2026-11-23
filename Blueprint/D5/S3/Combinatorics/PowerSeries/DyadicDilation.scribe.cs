using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class DyadicDilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/DyadicDilation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic power congruences hold at every degree.",
        H("Dyadic dilation of integral formal series"),
        Blocks(
            Paragraph(Text("In characteristic two, squaring sends every monomial to its degree doubling. Lifting the resulting difference of powers in the integer series ring raises the power of two that divides the difference. Repeating gives larger dilations at a fixed modulus.")),
            Node("reduce", "Reduce every integer coefficient modulo the given natural modulus.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("coeff_reduce_eq_zero", "A reduced coefficient vanishes exactly when the modulus divides the original coefficient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("map_mod_eq_iff", "Two reductions coincide exactly when the constant series of the modulus divides the difference.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("dyadic_lift", "The difference between the 2^(j+1)-th power and the 2^j-th power after degree doubling is divisible by the constant 2^(j+1).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("reduce_lift", "For every integral formal series p(q) and natural j and r, the coefficientwise reduction of p(q)^(2^(j+1+r)) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j) at the same modulus.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("reduce_lift_mul", "For every integral formal series p(q) and natural j, r and t, the coefficientwise reduction of p(q)^(2^(j+1+r)·t) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j·t) at the same modulus.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("dyadicdilation-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(narrative))), role);
}
