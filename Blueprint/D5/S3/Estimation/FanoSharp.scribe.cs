using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoSharpDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Estimation/FanoSharp",
            "Sharp finite Fano inequality replaces the frozen weak cardinality correction by the off-estimator cardinality and verifies consistency on their common range."),
        H("Sharp Finite Fano Inequality in Nats"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("sharp-fano-bounds-conditional-entropy-by-off-estimator-cardinality"),
                H("Sharp Fano uses the off-estimator cardinality"),
                LeanTheorem(
                    "D5/S3/Estimation/FanoSharp.fano_inequality_sharp"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("X"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Colon, Sp,
                    F.Id("Y"), Times, Sp, F.Id("X"), To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("g"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("X"), Comma, RowBreak,
                    F.Id("e"), Colon, Eq,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("y"), Comma, Sp, F.Id("x"), Colon, Sp,
                        F.Id("g"), Open, F.Id("y"), Close, Neq, Sp, F.Id("x")), Sp,
                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close, Comma, RowBreak,
                    Open,
                    Open,
                    Forall, Sp, F.Id("y"), Comma, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp,
                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close,
                    Close, Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("y"), Comma, Sp, F.Id("x")), Sp,
                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close,
                    Eq, D(1), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close,
                    Neq, Sp, D(1), Sp, Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("p"), Close,
                    Le, Sp,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Open, F.Id("b"), Colon, Sp,
                    Operatorname, Grp(F.Id("Bool")), Close, Mapsto, Sp,
                    F.Text, Grp(F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp),
                    F.Id("e"),
                    F.Text, Grp(Sp, F.Id("else"), Sp),
                    D(1), Minus, F.Id("e"), Close, Plus, Sp,
                    F.Id("e"), Sp, Log, Sp, Open,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close,
                    Minus, D(1), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "This theorem sharpens the frozen weak Fano inequality by replacing " +
                        "log(card X) with log(card X - 1). The latter counts only values that " +
                        "can differ from the estimator and is the form used in converse " +
                        "arguments. The weak theorem and its derivation remain frozen and are " +
                        "referenced rather than restated.")),
                    Paragraph(Text(
                        "The exclusion card X != 1 is a deliberate refusal to make the sharp " +
                        "statement range silently over the singleton. At card X = 1 its " +
                        "right-hand side contains Real.log 0, which Lean totalizes to zero. A " +
                        "claim over that case would therefore rest on totalization rather than " +
                        "on the analytic argument. This is precisely why the preceding wave " +
                        "declined to state the sharp form.")),
                    Paragraph(Text(
                        "The hypothesis is exactly the diagnosed obstruction and nothing more. " +
                        "Normalization supplies Nonempty X: because the total mass is one, some " +
                        "summand is nonzero and hence supplies an element of Y x X. Once " +
                        "cardinality one is ruled out, positivity of the finite cardinality " +
                        "gives 1 < card X. Consequently (card X : R) - 1 is nonzero, which is " +
                        "the condition required for the logarithm step.")),
                    Paragraph(Text(
                        "The singleton exclusion is documented by machine rather than merely " +
                        "by prose. A compiled witness takes Y = X = Unit, the unit-mass joint " +
                        "law, and the unique estimator, and evaluates the entire sharp " +
                        "right-hand side to zero. In particular, the witness records the " +
                        "totalized evaluation Real.log(card Unit - 1) = Real.log 0 = 0; it is " +
                        "not used to extend the theorem to the excluded case.")),
                    Paragraph(Text(
                        "The proof uses the same finite, nats-valued entropy infrastructure as " +
                        "the frozen result, but the error reference measure is supported only " +
                        "on points away from the estimator. Its total mass is card X - 1, and " +
                        "the frozen log-sum inequality then yields the sharper correction. No " +
                        "derivation of the weak form is repeated.")),
                    Paragraph(Text(
                        "The improvement is strict in a concrete finite model. Let Y = Unit, " +
                        "let X = Bool, take the uniform joint law, and use a constant estimator. " +
                        "Then e = 1/2 and card X = 2. The sharp correction is " +
                        "(1/2) log 1 = 0, whereas the weak correction is " +
                        "(1/2) log 2 > 0. Thus the sharp bound's correction term vanishes " +
                        "entirely for a binary estimand.")),
                    Paragraph(Text(
                        "All quantities are measured in nats. No binary-entropy definition is " +
                        "introduced: the two-point term is the shannonEntropy of a Bool law, " +
                        "exactly as in the frozen weak statement. The repository's bits-valued " +
                        "binaryEntropyBits remains unused for the unit-mismatch reason recorded " +
                        "in the weak form's document.")),
                    Paragraph(Text(
                        "The theorem claims no converse direction, minimax or sample-complexity " +
                        "corollary, equality characterization, or measure-theoretic analogue. " +
                        "Its scope is the finite sharp upper bound under the exact singleton " +
                        "exclusion displayed above.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("sharp-fano-right-hand-side-is-bounded-by-the-weak-right-hand-side"),
                H("The sharp Fano right-hand side implies the weak one"),
                LeanTheorem(
                    "D5/S3/Estimation/FanoSharp.fano_sharp_rhs_le_weak_rhs"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("e"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    D(0), Le, Sp, F.Id("e"), Sp, Land, Sp,
                    D(1), Lt, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Open, F.Id("b"), Colon, Sp,
                    Operatorname, Grp(F.Id("Bool")), Close, Mapsto, Sp,
                    F.Text, Grp(F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp),
                    F.Id("e"),
                    F.Text, Grp(Sp, F.Id("else"), Sp),
                    D(1), Minus, F.Id("e"), Close, Plus, Sp,
                    F.Id("e"), Sp, Log, Sp, Open,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close,
                    Minus, D(1), Close, Le, Sp, RowBreak,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Open, F.Id("b"), Colon, Sp,
                    Operatorname, Grp(F.Id("Bool")), Close, Mapsto, Sp,
                    F.Text, Grp(F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp),
                    F.Id("e"),
                    F.Text, Grp(Sp, F.Id("else"), Sp),
                    D(1), Minus, F.Id("e"), Close, Plus, Sp,
                    F.Id("e"), Sp, Log, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The named theorem fano_sharp_rhs_le_weak_rhs proves that the sharp " +
                        "right-hand side is at most the frozen weak right-hand side whenever " +
                        "the error mass is nonnegative and 1 < card X. This obligation is part " +
                        "of the sharpening: a proposed stronger statement that failed to imply " +
                        "the result it sharpens would expose an error in the new statement. The " +
                        "overlap between old and new results is the least costly place to detect " +
                        "such an error, so the two bounds are proved visibly consistent rather " +
                        "than left merely to coexist.")))))));
}
