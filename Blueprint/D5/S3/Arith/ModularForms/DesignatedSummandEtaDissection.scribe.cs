using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class DesignatedSummandEtaDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");
    private static readonly LibraryNoteRef Sellers = LibraryNoteRef.Create("D5/L/Fourier/sellers2023designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity dissections of the designated-summand generating series and its inverse.",
        H("Integral reciprocal and square dissections"),
        Blocks(
            Paragraph(Text("The Jacobi product identities turn the parity dissection into an identity between Euler units. The coefficient map from integers to rationals is injective, so the reciprocal dissection holds integrally. Pairing odd Euler factors at q and −q gives the sign norm used to square F. The factor W reduces modulo four to f6 squared, which is supported on even degrees.")),
            Paragraph(Text("Lemma 2.2 of Yaqubi and Mirzavaziri gives the prime-power Frobenius congruence. The dyadic lift uses the iterated Frobenius over ZMod 2, then raises the integral congruence to the required modulus.")),
            Node("reduce", "Reduce every integer coefficient modulo the given natural modulus.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("coeff_reduce_eq_zero", "A reduced coefficient vanishes exactly when the modulus divides the original coefficient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("map_mod_eq_iff", "Two reductions coincide exactly when the constant series of the modulus divides the difference.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("reduce_lift", "For every integral formal series p(q) and natural j and r, the coefficientwise reduction of p(q)^(2^(j+1+r)) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j) at the same modulus.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("reduce_lift_mul", "For every integral formal series p(q) and natural j, r and t, the coefficientwise reduction of p(q)^(2^(j+1+r)·t) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j·t) at the same modulus.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("H", "The inverse unit of the generating series F.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("H0", "The Euler quotient f1^2 f4^2 f6^4 divided by f2^2 f3^2 f12^2, whose degree doubling is the even part of H over the integers.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("T", "The Euler quotient f1^4 f6^2 divided by f2^2 f3^2. Over the integers, the odd part of H is −q T(q⁴).", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("FH", "The product of F and H is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("H_dissection", "Over the integers, H(q) is H0(q²) minus q T(q⁴).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Sellers)),
            Node("H_support", "The integral coefficient of H in degree 4n+3 vanishes for every natural n.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("E", "The integral series such that E(q²) is the even part of F(q) squared.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("W", "The integral Euler quotient f2^4 f6^4 divided by f1^8 f3^4.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("F_square", "Over the integers, F(q) squared is E(q²) plus 2q W(q²).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("W_support", "For every natural n, the coefficient of degree 2n+1 in the integral series W is divisible by four.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("designatedsummandetadissection-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(narrative))), role);
}
