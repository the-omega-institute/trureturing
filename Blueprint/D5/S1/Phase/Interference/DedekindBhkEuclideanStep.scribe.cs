using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DedekindBhkEuclideanStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite Dedekind base and Euclidean reciprocity step hold, while a nonzero-walk certificate refutes the requested sign.",
        H("Dedekind BHK Base, Euclidean Step, and Sign Obstruction"),
        Blocks(
            Paragraph(Text(
                "The frozen finite-residue formula evaluates the one-coefficient base. "
                    + "The frozen reciprocity theorem and numerator periodicity then give one "
                    + "exact Euclidean continued-fraction shift.")),
            Describe.Lean(
                DescribeId.Create("dedekind-sum-one-closed"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkEuclideanStep."
                    + "dedekind_sum_one_closed"),
                H("The one-coefficient base"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Esc, F.Id("c"), Gt, D(0), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(1), Comma, Sp, F.Id("c"), Close,
                    Sp, Eq, Sp,
                    Frac,
                    Grp(Open, F.Id("c"), Minus, D(1), Close,
                        Open, F.Id("c"), Minus, D(2), Close),
                    Grp(D(1, 2), F.Id("c"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After reducing the second residue with numerator one, every summand is a "
                        + "sawtooth square. The frozen linear and square sums give the displayed value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bhk-plus-walk-single-coefficient"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkEuclideanStep."
                    + "bhk_plus_walk_single_coefficient"),
                H("The corrected one-coefficient BHK base"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Esc, F.Id("c"), Gt, D(0), Sp, Rightarrow, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(1), Comma, Sp, F.Id("c"), Close,
                    Sp, Eq, Sp, Minus, D(3), Sp, Plus, Sp,
                    Frac, Grp(D(1), Plus, D(1)), Grp(F.Id("c")), Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, F.Id("c"), CloseBracket, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substituting the closed base value and unfolding the frozen one-term walk "
                        + "gives the BHK equation with a plus walk. This is already incompatible "
                        + "with the requested minus-walk orientation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dedekind-reciprocity-cf-step"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkEuclideanStep."
                    + "dedekind_reciprocity_cf_step"),
                H("One Euclidean continued-fraction shift"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Comma, Sp, F.Id("d"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("c"), Gt, D(0), Sp, Land, Sp,
                    F.Id("d"), Gt, D(0), Sp, Land, Sp,
                    Gcd, Open, F.Id("c"), Comma, Sp, F.Id("d"), Close,
                    Eq, D(1), Sp, Rightarrow, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("d"), Comma, Sp, F.Id("c"), Close,
                    Sp, Eq, Sp, Minus, D(3), Sp, Plus, Sp,
                    Frac, Grp(F.Id("c")), Grp(F.Id("d")), Sp, Plus, Sp,
                    Frac, Grp(F.Id("d")), Grp(F.Id("c")), Sp, Plus, Sp,
                    Frac, Grp(D(1)), Grp(F.Id("c"), F.Id("d")), Sp, Minus, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("c"), Sp, Operatorname, Grp(F.Id("mod")), Sp, F.Id("d"),
                    Comma, Sp, F.Id("d"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Dedekind reciprocity supplies the explicit rational correction and flips the "
                        + "sum orientation. The periodicity theorem replaces the reversed numerator "
                        + "by its Euclidean remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bhk-minus-walk-counterexample"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindBhkEuclideanStep."
                    + "bhk_minus_walk_counterexample"),
                H("A nonzero-walk sign counterexample"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1)), Grp(D(2), Plus,
                        Frac, Grp(D(1)), Grp(D(1), Plus, Frac, Grp(D(1)), Grp(D(1)))),
                    Sp, Eq, Sp, Frac, Grp(D(2)), Grp(D(5)), Sp, Land, Sp,
                    Open, D(3), Times, D(2), Close, Sp,
                    Operatorname, Grp(F.Id("mod")), Sp, D(5), Sp, Eq, Sp, D(1),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(2), Comma, Sp, D(1), Comma, Sp, D(1), CloseBracket, Close,
                    Sp, Eq, Sp, D(2), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(2), Comma, Sp, D(5), Close, Sp, Eq, Sp, D(0),
                    Sp, Land, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(2), Comma, Sp, D(5), Close,
                    Sp, Neq, Sp, Minus, D(3), Sp, Plus, Sp,
                    Frac, Grp(D(3), Plus, D(2)), Grp(D(5)), Sp, Minus, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(2), Comma, Sp, D(1), Comma, Sp, D(1), CloseBracket, Close,
                    Sp, Land, Sp,
                    D(1, 2), Times,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(2), Comma, Sp, D(5), Close,
                    Sp, Eq, Sp, Minus, D(3), Sp, Plus, Sp,
                    Frac, Grp(D(3), Plus, D(2)), Grp(D(5)), Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(2), Comma, Sp, D(1), Comma, Sp, D(1), CloseBracket, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive odd expansion [0; 2, 1, 1] equals two fifths, three is the "
                        + "normalized inverse of two modulo five, and the frozen alternating walk "
                        + "equals two. The exact Dedekind sum is zero. Consequently the source's "
                        + "minus-walk equation is false here, while the plus-walk equation is exact.")),
                    Paragraph(Text(
                        "The two earlier certificates both have zero alternating walk and therefore "
                            + "cannot distinguish these signs. The general finale remains open pending "
                            + "a corrected authoritative statement."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/WalkFormula")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindBhkCertificates")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindReciprocityFiniteSums")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindReciprocity")),
        ]));
}
