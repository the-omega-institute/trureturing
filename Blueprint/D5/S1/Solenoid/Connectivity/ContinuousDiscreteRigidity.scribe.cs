using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid.Connectivity;

internal sealed class ContinuousDiscreteRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous map from a connected space to a discrete space is constant.",
        H("Continuous Discrete Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-maps-from-connected-to-discrete-are-constant"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity."
                        + "continuous_map_to_discrete_is_constant"),
                H("A continuous map from connected to discrete is constant"),
                StatementSource.FromAuthor(ContinuousDiscreteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be connected and Y carry the discrete topology. For an arbitrary "
                            + "continuous map T from X to Y, any two values T(x) and T(y) are "
                            + "equal.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies PreconnectedSpace.constant, which is applied "
                            + "directly after connectedness supplies the preconnected-space "
                            + "instance. Repository search found no duplicate map theorem."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula ContinuousDiscreteFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula t = F.Id("T");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, yType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Typeclass("TopologicalSpace", xType), Comma, Sp,
            Typeclass("ConnectedSpace", xType), Comma, Esc,
            Typeclass("TopologicalSpace", yType), Comma, Sp,
            Typeclass("DiscreteTopology", yType), Comma, Esc,
            t, Colon, Sp, xType, Sp, To, Sp, yType, Comma, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("Continuous"))), t), Sp,
            Rightarrow, RowBreak,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, xType, Comma, Sp,
            Apply(t, x), Sp, Eq, Sp, Apply(t, y), Dot));
    }
}
