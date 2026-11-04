using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA378258ModSixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA378258ModSix.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a378258");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every normalized solution of Hanna's system has coefficients avoiding one and five modulo six beyond degree one.",
        H("Hanna's Modulo-Six Conjecture"),
        Blocks(
            Paragraph(Text("PowerSeries is the ring of formal power series and X is its indeterminate. "
                + "The expression PowerSeries.subst(u,f) means f(u(X)); the inner series is the first argument. "
                + "The coefficient operator coeff(n,A) extracts the coefficient of X to the power n. "
                + "The integer z is cast to the rationals when compared with a rational coefficient.")),
            Node("claim", "The separate modulo-six assertion", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "The unpaginated OEIS A378258 Comments state: \"Conjecture: a(n) is not congruent to 1 nor 5 (mod 6) for n > 1.\" "
                + "IsGF is the original HannaA378258SquareRootParity.IsGF over rational formal power series. "
                + "It requires constant coefficient zero, linear coefficient one, A=B+5A squared, and B(A-A squared)=X "
                + "for some rational series B. A normalized solution exists, and the conclusion covers every such solution "
                + "and every natural degree strictly greater than one. The symbol emod denotes Int.emod and uses the nonnegative remainder modulo six.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Exclusion of the two residues", Disp(ClaimBody()),
                "Reuse the frozen existence, integrality and dyadic-parity result. An integer coefficient lift of any "
                + "normalized rational solution satisfies (F-5F squared) composed with (F-F squared)=X, because the "
                + "integer-to-rational coefficient map is injective and commutes with substitution at zero constant term. "
                + "Modulo three, F+F squared and F-F squared are compositional inverses. "
                + "For any commutative domain in which two is nonzero, this normalized inverse-pair system has at most "
                + "one solution: composition with F+F squared produces a normalized Catalan solution; Mathlib uniqueness of the "
                + "compositional inverse of X-X squared identifies these solutions, and the existing half_unique identifies their auxiliary "
                + "compositional square roots. The unit 1+F+G then identifies F and G. "
                + "Swapping the two inverse series and conjugating by X mapped to minus X makes -F(-X) another solution. "
                + "Uniqueness therefore proves F=-F(-X), rather than assuming symmetry. Every even-degree coefficient "
                + "vanishes modulo three. If the original integer coefficient is odd, frozen dyadic parity makes its "
                + "degree a power of two; a power of two greater than one is even, so that coefficient is divisible "
                + "by three. An even integer, or an odd integer divisible by three, cannot have remainder one or five "
                + "modulo six. Degree zero enters the coefficient lift via normalization; degree one is excluded by "
                + "the source conjecture. No finite truncation is used. The derivation reuses existing algebraic "
                + "interfaces; it claims no global priority. The source-family registration reconstructs the complete original "
                + "claim, proves whole-family variation and sensitivity, and witnesses coefficient dependence at "
                + "degrees two and three of an actual normalized solution. Its continuation is unknown; no claim "
                + "of undecidability or inexhaustibility follows. This delivery awaits independent review and freezing.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a378258-hanna-mod-six"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("hanna-a378258-mod-six-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula ClaimBody()
    {
        var a = F.Id("A"); var n = F.Id("n"); var z = F.Id("z");
        Formula IsGf(Formula value) => Call("IsGF", value);
        Formula Excludes(byte residue) => Seq(Call("emod", z, D(6)), Sp, Neq, Sp, D(residue));
        return And(Some("A", Series(), IsGf(a)),
            All("A", Series(), Arrow(IsGf(a), All("n", Naturals(),
                Arrow(Seq(D(1), Sp, Lt, Sp, n), Some("z", Integers(),
                    And(Equal(Call("coeff", n, a), Parenthesized(Seq(z, Colon, Sp, Rationals()))),
                        And(Excludes(1), Excludes(5)))))))));
    }
}
