using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums.Fermat;

internal sealed class CubicFermatTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/Fermat/CubicFermatTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cubic Fermat projective point count is the residue cardinality plus one minus the trace of a primary Eisenstein generator.",
        H("Cubic Fermat Counts and Eisenstein Traces"),
        Blocks(
            Paragraph(Text(
                "Let E = Z[omega] with omega^2 + omega + 1 = 0. The concrete embedding into C sends omega to "
                + "(-1 + i sqrt(3))/2. It is injective, and twice the real part of the image of an Eisenstein integer "
                + "is its integral quadratic-algebra trace. For a finite field F, write q = card F. "
                + "Point counts below are cardinalities of the actual projective "
                + "subtype defined in CharacterPointCount.")),
            Describe.Lean(
                DescribeId.Create("cubic-fermat-complex-count"),
                DeclarationHandle.Create(Prefix + "cubic_projective_count"),
                H("The cubic count is a conjugate pair of Jacobi sums"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("F"), Comma, Sp, Call("finiteField", F.Id("F")), Comma, Sp,
                    F.Id("chi"), Colon, Sp, Call("MulChar", F.Id("F"), F.Id("C")), Comma, Sp,
                    Call("orderOf", F.Id("chi")), Eq, D(3), Sp, Implies, Sp,
                    Count(F.Id("F")), Eq, Call("card", F.Id("F")), Plus, D(1), Plus,
                    D(2), Call("Re", Call("J", F.Id("chi"), F.Id("chi")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specialize the projective character-sum formula to degree three. Exact character order gives "
                    + "chi^2 = chi^{-1}, so only J(chi,chi) and J(chi^{-1},chi^{-1}) remain. Complex conjugation "
                    + "identifies these two Jacobi sums. Taking real parts gives q + 1 + 2 Re J."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-fermat-integral-trace"),
                DeclarationHandle.Create(Prefix + "cubic_projective_count_integral"),
                H("An Eisenstein-valued character gives an integral trace formula"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("F"), Comma, Sp, Call("finiteField", F.Id("F")), Comma, Sp,
                    F.Id("chi"), Colon, Sp, Call("MulChar", F.Id("F"), F.Id("E")), Comma, Sp,
                    Call("orderOf", F.Id("chi")), Eq, D(3), Sp, Implies, Sp,
                    Count(F.Id("F")), Eq, Call("card", F.Id("F")), Plus, D(1), Plus,
                    Call("Tr", Call("J", F.Id("chi"), F.Id("chi")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Transport the same character through the concrete injective embedding. Its order remains three, "
                    + "and ring-homomorphism compatibility transports the Jacobi sum. Replace twice its real part "
                    + "by the integral trace and descend the resulting equality to Z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-fermat-primary-count"),
                DeclarationHandle.Create(Prefix + "cubic_projective_count_primary"),
                H("The primary generator determines the exact projective count"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("P"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
                    Call("maximal", F.Id("P")), Comma, Sp, Call("finite", Quotient()), Comma, Sp,
                    Call("mod", Call("card", Quotient()), D(3)), Eq, D(1), Comma, Sp,
                    F.Id("pi"), Colon, Sp, F.Id("E"), Comma, Sp,
                    Call("spanSingleton", F.Id("pi")), Eq, F.Id("P"), Comma, Sp,
                    Call("divides", D(3), F.Seq(F.Id("pi"), Minus, D(1))),
                    Sp, Implies, Sp, Count(Quotient()), Eq,
                    Call("card", Quotient()), Plus, D(1), Minus, Call("Tr", F.Id("pi"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The cardinality congruence excludes characteristic three: if 3 belonged to P, the finite "
                        + "residue field would have characteristic three and cardinality divisible by three. "
                        + "Use the actual zero-extended Euler character attached to P. The preceding Jacobi normalization "
                        + "proves -J = pi for this same character and ideal. Applying the integral trace yields "
                        + "card(projectivePoints(E/P,3)) = card(E/P) + 1 - Tr(pi). "
                        + "Neither a Jacobi value nor a norm identity is assumed by the point-count theorem.")),
                    Paragraph(Text(
                        "These are classical character-sum point-count identities, with no mathematical novelty claim. "
                        + "The formal bridge joins the actual projective point set, the fixed Euler character, the concrete "
                        + "complex embedding and the primary generator. It applies to all finite residue fields satisfying "
                        + "the stated assumptions, including prime-power cardinalities."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Quotient() => Call("quotient", F.Id("E"), F.Id("P"));
    private static Formula Count(Formula field) => Call("card", Call("projectivePoints", field, D(3)));
}
