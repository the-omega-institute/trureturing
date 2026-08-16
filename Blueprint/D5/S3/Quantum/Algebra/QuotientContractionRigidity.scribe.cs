using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class QuotientContractionRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict contraction on a closed-subspace quotient has no nonzero fixed class.",
        H("Quotient Contraction Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-strict-quotient-contraction-has-no-nonzero-fixed-class"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/QuotientContractionRigidity."
                    + "quotient_contraction_rigidity"),
                H("A strict quotient contraction has no nonzero fixed class"),
                StatementSource.FromAuthor(QuotientContractionRigidityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be a nontrivially normed field, H a normed space over k, M a "
                            + "closed subspace, and R a continuous linear endomorphism preserving "
                            + "M. If R fixes x modulo M and the induced operator on H modulo M "
                            + "has norm strictly less than one, then x lies in M.")),
                    Paragraph(Text(
                        "The invariant-subspace hypothesis constructs the quotient operator via "
                            + "the canonical continuous quotient map and its continuous lift. The "
                            + "class of x is fixed because R x minus x belongs to M. Its norm is "
                            + "therefore at most the operator norm times itself; strict contraction "
                            + "forces that quotient norm to vanish, and closedness identifies the "
                            + "zero quotient class with membership in M.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact rigidity theorem. "
                            + "Pinned Mathlib supplies Submodule.mkQL, Submodule.liftQL, "
                            + "ContinuousLinearMap.le_opNorm, and the quotient zero-class lemma, "
                            + "which are composed directly. Loogle returned no exact match, and "
                            + "three GitHub Lean-code searches returned no hits. The LeanSearch "
                            + "API request failed, so it is not counted as a negative result."))),
                DescribeRole.Theorem))));

    private static Formula QuotientContractionRigidityFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula subspace = F.Id("M");
        Formula map = F.Id("R");
        Formula invariant = F.Id("h");
        Formula x = F.Id("x");
        Formula quotientMap = Call("inducedQuotientMap", subspace, map, invariant);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NontriviallyNormedField")),
            Open, scalar, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")),
            Open, space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedSpace")), Underscore, Grp(scalar),
            Open, space, Close, CloseBracket, Comma, Esc,
            subspace, Colon, Sp, Operatorname, Grp(F.Id("Submodule")), Underscore,
            Grp(scalar), Open, space, Close, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("IsClosed")), Open, subspace, Close,
            CloseBracket, Comma, Esc,
            map, Colon, Sp, space, Sp, To, Sp, space, Comma, Esc,
            invariant, Colon, Sp, map, Open, subspace, Close, Sp, Subseteq, Sp,
            subspace, Comma, Esc,
            x, Colon, Sp, space, Comma, Esc,
            Open, map, Open, x, Close, Sp, Minus, Sp, x, Sp, InMacro, Sp, subspace,
            Sp, Land, Sp,
            Call("norm", quotientMap), Sp, Lt, Sp, D(1), Close,
            Sp, Rightarrow, Sp, x, Sp, InMacro, Sp, subspace, Dot));
    }
}
