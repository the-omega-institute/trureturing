using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class CanonicalVerdictReductionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/VisibleDescent/CanonicalVerdictReduction."
            + "canonical_verdict_reduction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Verdict tables descend canonically, reduce by column representatives, and remain "
            + "relative to the implementation population.",
        H("Canonical Verdict Reduction"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-verdict-reduction"),
            DeclarationHandle.Create(Declaration),
            H("The true verdict source is its population-relative double quotient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The implementation kernel is equality of complete verdict rows, and the "
                        + "test kernel is equality of complete verdict columns. Mathlib's "
                        + "two-quotient lift gives the displayed canonical verdict map; its "
                        + "representative computation rule determines that map uniquely.")),
                Paragraph(Text(
                    "A retained test subset is lossless when every original test has a retained "
                        + "test with the same column. Such a subset is inclusion-minimal among "
                        + "lossless subsets exactly when it contains one representative of every "
                        + "column class.")),
                Paragraph(Text(
                    "Two distinct tests can agree on every current implementation and cease to "
                        + "agree after one implementation is adjoined. Redundancy is therefore "
                        + "indexed by the chosen implementation population.")),
                Paragraph(Text(
                    "The canonical descent and extension witness are imported from their frozen "
                        + "D5 owners. Repository and pinned-Mathlib searches found no existing "
                        + "minimal-lossless-subset characterization with this verdict-column shape."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula implementationType = F.Id("Implementation");
        Formula testType = F.Id("Test");
        Formula verdict = F.Id("r");
        Formula implementationKernel = F.Id("implementationKernel");
        Formula testKernel = F.Id("testKernel");
        Formula canonicalVerdict = F.Id("canonicalVerdict");
        Formula implementation = F.Id("i");
        Formula secondImplementation = F.Id("j");
        Formula test = F.Id("t");
        Formula secondTest = F.Id("u");
        Formula other = F.Id("f");
        Formula kept = F.Id("kept");
        Formula candidate = F.Id("candidate");
        Formula representative = F.Id("q");
        Formula extended = F.Id("rPrime");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula boolType = Seq(Operatorname, Grp(F.Id("Bool")));
        Formula implementationQuotient = Call("Quotient", implementationKernel);
        Formula testQuotient = Call("Quotient", testKernel);
        Formula quotientVerdictType =
            Arrow(implementationQuotient, Arrow(testQuotient, boolType));
        Formula testSetType = Call("Set", testType);
        Formula implementationRow = Seq(
            LambdaLower, Sp, Typed(implementation, implementationType), Comma, Sp,
            LambdaLower, Sp, Typed(test, testType), Comma, Sp,
            Apply(verdict, implementation, test));
        Formula testColumn = Seq(
            LambdaLower, Sp, Typed(test, testType), Comma, Sp,
            LambdaLower, Sp, Typed(implementation, implementationType), Comma, Sp,
            Apply(verdict, implementation, test));

        Formula representativeInvariance = Seq(
            Forall, Sp,
            Typed(implementation, implementationType), Comma, Sp,
            Typed(secondImplementation, implementationType), Comma, Sp,
            Typed(test, testType), Comma, Sp,
            Typed(secondTest, testType), Comma, Sp,
            Apply(implementationKernel, implementation, secondImplementation), Sp, Land, Sp,
            Apply(testKernel, test, secondTest), Sp, Rightarrow, Sp,
            Apply(verdict, implementation, test), Sp, Eq, Sp,
            Apply(verdict, secondImplementation, secondTest));
        Formula representativeComputation = Seq(
            Forall, Sp,
            Typed(implementation, implementationType), Comma, Sp,
            Typed(test, testType), Comma, Sp,
            Apply(canonicalVerdict, Call("class", implementation), Call("class", test)),
            Sp, Eq, Sp, Apply(verdict, implementation, test));
        Formula otherComputes = Seq(
            Forall, Sp,
            Typed(implementation, implementationType), Comma, Sp,
            Typed(test, testType), Comma, Sp,
            Apply(other, Call("class", implementation), Call("class", test)),
            Sp, Eq, Sp, Apply(verdict, implementation, test));
        Formula descentUniqueness = Seq(
            Forall, Sp, Typed(other, quotientVerdictType), Comma, Sp,
            Open, otherComputes, Close, Sp, Rightarrow, Sp,
            other, Sp, Eq, Sp, canonicalVerdict);

        Formula losslessKept = Lossless(kept, representative, test, testType, testKernel);
        Formula losslessCandidate =
            Lossless(candidate, representative, test, testType, testKernel);
        Formula inclusionMinimal = Seq(
            Forall, Sp, Typed(candidate, testSetType), Comma, Sp,
            candidate, Sp, Subseteq, Sp, kept, Sp, Land, Sp,
            Open, losslessCandidate, Close, Sp, Rightarrow, Sp,
            kept, Sp, Subseteq, Sp, candidate);
        Formula uniqueRepresentatives = Seq(
            Forall, Sp, Typed(test, testType), Comma, Sp,
            Exists, Bang, Sp, representative, Comma, Sp,
            Member(representative, kept), Sp, Land, Sp,
            Apply(testKernel, representative, test));
        Formula reduction = Seq(
            Forall, Sp, Typed(kept, testSetType), Comma, Sp,
            Open, Open, losslessKept, Close, Sp, Land, Sp,
            Open, inclusionMinimal, Close, Close, Sp, Iff, Sp,
            Open, uniqueRepresentatives, Close);

        Formula extension = Seq(
            Forall, Sp,
            Typed(test, testType), Comma, Sp,
            Typed(secondTest, testType), Comma, Sp,
            test, Sp, Neq, Sp, secondTest, Sp, Land, Sp,
            Apply(testKernel, test, secondTest), Sp, Rightarrow, Sp,
            Exists, Sp,
            Typed(extended, Arrow(Call("Option", implementationType),
                Arrow(testType, boolType))), Comma, Sp,
            Open, Forall, Sp, Typed(implementation, implementationType), Comma, Sp,
            Apply(extended, Call("some", implementation)), Sp, Eq, Sp,
            Apply(verdict, implementation), Close, Sp, Land, Sp,
            Apply(extended, F.Id("none"), test), Sp, Neq, Sp,
            Apply(extended, F.Id("none"), secondTest));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(implementationType, Comma, Sp, testType), type), Comma),
            Seq(
                Typed(verdict, Arrow(implementationType, Arrow(testType, boolType))), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                implementationKernel, Sp, Colon, Eq, Sp,
                Call("ker", implementationRow), Comma),
            Seq(
                testKernel, Sp, Colon, Eq, Sp,
                Call("ker", testColumn), Comma),
            Seq(
                canonicalVerdict, Sp, Colon, Sp, quotientVerdictType, Sp, Colon, Eq, Sp,
                Call("QuotientLift2", verdict, implementationKernel, testKernel), Sp,
                Operatorname, Grp(F.Id("in"))),
            Seq(Open, representativeInvariance, Close, Sp, Land),
            Seq(Open, representativeComputation, Close, Sp, Land),
            Seq(Open, descentUniqueness, Close, Sp, Land),
            Seq(Open, reduction, Close, Sp, Land),
            Seq(Open, extension, Close, Dot),
        ]));
    }

    private static Formula Lossless(
        Formula set,
        Formula representative,
        Formula test,
        Formula testType,
        Formula testKernel) => Seq(
            Forall, Sp, Typed(test, testType), Comma, Sp,
            Exists, Sp, representative, Comma, Sp,
            Member(representative, set), Sp, Land, Sp,
            Apply(testKernel, representative, test));

    private static Formula Member(Formula element, Formula set) =>
        Seq(element, Sp, InMacro, Sp, set);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
