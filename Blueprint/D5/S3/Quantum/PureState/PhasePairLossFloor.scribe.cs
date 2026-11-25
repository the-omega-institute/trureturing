using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhasePairLossFloorDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/PureState/PhasePairLossFloor.mixed_lower_coefficient_iff";

    private static Formula V(string name) => F.Id(name);
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Sub(string name, Formula index) => new Formula.Subscript(V(name), index);
    private static Formula Sq(Formula x) => new Formula.Power(x, D(2));
    private static Formula Ratio(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Par(params Formula[] items) => Seq(Open, Seq(items), Close);
    private static Formula Index(string name, Formula size) =>
        Seq(D(1), Le, Sp, V(name), Le, Sp, size);
    private static Formula Loss(string readout) =>
        Seq(V("L"), Par(V(readout), Comma, V("p"), Comma, V("v")));
    private static Formula Coefficient() => Ratio(
        Seq(D(9), Par(D(3), Plus, Sq(V("R")))),
        Seq(D(1, 6), Par(D(2), Plus, Sq(V("R")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp lower comparison of the simplex and cube losses for two coordinates.",
        H("Two-coordinate loss comparison on a closed disk"),
        Blocks(Describe.Lean(DescribeId.Create("phase-pair-sharp-lower-coefficient"),
            DeclarationHandle.Create(Declaration),
            H("Exact lower loss coefficients"),
            StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Amp, Forall, Sp, V("R"), Comma, V("C"), InMacro, Sp, Field("R"), Comma,
                    D(0), Le, Sp, V("R"), Rightarrow, Sp, Open),
                Seq(Amp, Open,
                    Forall, Sp, V("m"), InMacro, Sp, Field("N"), Comma,
                    V("p"), InMacro, Sp, Seq(Field("R"), Caret, Grp(V("m"))), Comma,
                    V("v"), InMacro, Sp, Seq(Field("C"), Caret, Grp(V("m"), Times, D(2))), Comma),
                Seq(Amp,
                    Par(
                        Par(Forall, Sp, Index("i", V("m")), Comma, Index("j", V("m")), Comma,
                            Sub("p", V("i")), Sub("p", V("j")), Ge, D(0)),
                        Land, Sp,
                        Par(Forall, Sp, Index("i", V("m")), Comma, Sub("p", V("i")), Neq, D(0),
                            Rightarrow, Sp, Forall, Sp, Index("k", D(2)), Comma,
                            new Formula.Absolute(Sub("v", Seq(V("i"), V("k")))), Le, Sp, V("R"))),
                    Rightarrow, Sp, V("C"), Loss("A"), Le, Sp, Loss("B"), Close),
                Seq(Amp, Leftrightarrow, Sp, Begin, Grp(V("cases")),
                    V("C"), Le, Sp, Coefficient(), Amp, V("R"), Le, D(1), RowBreak,
                    V("C"), Eq, Ratio(D(3), D(4)), Amp, V("R"), Gt, D(1),
                    End, Grp(V("cases")), Close)
            ]))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Here A is the simplex overlap, B is the cube overlap and L is the "
                    + "weighted sum of pairwise deficits. Each coordinate of a relative row is "
                    + "the product of one conjugated coordinate and the corresponding coordinate "
                    + "of another row. The relative coordinates of pairs of nonzero weight have "
                    + "modulus at most the square of the disk radius.")),
                Paragraph(Text("Write x for the mean of the two real parts of a relative row. "
                    + "The difference between the cube deficit and C times the simplex deficit "
                    + "is the sum of three terms.")),
                new DocumentBlock.DisplayFormula(Seq(Par(D(1), Minus, V("x")),
                        Par(Ratio(Seq(D(3), Plus, V("x")), D(4)), Minus,
                            V("C"), Ratio(Seq(D(4), Par(D(2), Plus, V("x"))), D(9))),
                        Plus, Ratio(Sq(Par(Sub("a", D(1)), Minus, Sub("a", D(2)))), D(1, 6)),
                        Plus, V("C"), Ratio(Sq(Par(Sub("b", D(1)), Plus, Sub("b", D(2)))), D(9)))),
                Paragraph(Text("The a coordinates are real parts and the b coordinates are imaginary "
                    + "parts. At the displayed coefficient for a radius at most one, the factor "
                    + "multiplying one minus x simplifies to the following nonnegative quotient.")),
                new DocumentBlock.DisplayFormula(Ratio(Seq(Sq(V("R")), Minus, V("x")),
                    Seq(D(4), Par(D(2), Plus, Sq(V("R")))))),
                Paragraph(Text("All three terms are nonnegative. The simplex deficit is also nonnegative "
                    + "on these disks, which gives the inequality for every smaller coefficient. "
                    + "At three quarters the first term is the square of one minus x divided by twelve, "
                    + "giving the inequality for arbitrary complex relative coordinates.")),
                Paragraph(Text("A single row of weight one with both coordinates equal to a real t "
                    + "has both relative coordinates equal to t squared. The two square remainders "
                    + "vanish. When the radius is below one, taking t equal to the radius forces "
                    + "the stated upper endpoint on C. At radius one, taking t up to one gives "
                    + "the endpoint three quarters. For a radius greater than one, taking t down "
                    + "to one gives the reverse restriction because one minus t squared changes sign.")),
                Paragraph(Text("For probability weights and unit-modulus coordinates the losses "
                    + "are deficits of mixture purity. The larger disks extend the algebraic "
                    + "comparison to arbitrary complex coordinates within the radius bound."))),
            DescribeRole.Theorem))));
}
