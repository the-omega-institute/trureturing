using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class ObserverDiagonalSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An information-complete quantum readout coexists with diagonal escape.",
        H("Observer Diagonal Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("context-readout"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/ObserverDiagonalSeparation.contextReadout"),
                H("Projector-trace context readout"),
                StatementSource.FromAuthor(ReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout is built directly from the canonical rank-one context carrier: "
                        + "each coordinate is the complex trace of the state matrix times the "
                        + "named context projector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("empirical-observer-diagonal-separation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/ObserverDiagonalSeparation."
                        + "empirical_observer_diagonal_separation"),
                H("Empirical observer and diagonal separation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The witness uses the repository's exact rank-one context and matrix "
                            + "carrier. Complementary overlaps are public, and the resulting "
                            + "projector-trace readout is injective on all one-dimensional complex "
                            + "matrices by the imported tomography theorem.")),
                    Paragraph(Text(
                        "Independently, a Unit-indexed Boolean evaluation list and a Boolean "
                            + "fixed-point-free twist satisfy the public diagonal non-capture clause "
                            + "by the imported Lawvere escape theorem.")),
                    Paragraph(Text(
                        "Search found both exact supporting declarations but no combined existential; "
                            + "the two carriers and all hypotheses remain explicit in the statement."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula ReadoutFormula()
    {
        Formula n = F.Id("n");
        Formula context = F.Id("context");
        Formula rho = F.Id("rho");
        Formula l = F.Id("l");
        Formula j = F.Id("j");
        Formula matrix = Operatorname;

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            context, Colon, Sp,
            Arrow(Seq(Operatorname, Grp(F.Id("Fin")), Open, Seq(n, Plus, D(2)), Close),
                Call("RankOneContext", Seq(n, Plus, D(1)))), Comma, Sp,
            rho, Colon, Sp,
            Call("Matrix", Seq(Operatorname, Grp(F.Id("Fin")), Open, Seq(n, Plus, D(1)), Close),
                Seq(Operatorname, Grp(F.Id("Fin")), Open, Seq(n, Plus, D(1)), Close), F.Id("Complex")), Comma, RowBreak, Grp(),
            Call("contextReadout", context, rho), Sp, Eq, Sp,
            Call("fun", l, j, Sp, Call("trace", Call("mul", rho,
                Call("projector", context, l, j)))), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula context = F.Id("context");
        Formula l = F.Id("l");
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula r = F.Id("r");
        Formula evaluation = F.Id("evaluation");
        Formula twist = F.Id("twist");
        Formula y = F.Id("y");
        Formula a = F.Id("a");
        Formula overlap = Seq(
            Call("trace", Call("mul", Call("projector", context, l, j),
                Call("projector", context, k, r))), Sp, Eq, Sp,
            Call("if", Call("Eq", l, k),
                Call("if", Call("Eq", j, r), D(1), D(0)),
                Call("inverse", D(1))));
        Formula readout = Call("Injective", Call("contextReadout", context));
        Formula diagonal = Seq(
            Call("fun", a, Sp, Call("twist",
                Call("evaluation", a, a))), Sp,
            Neg, Sp, InMacro, Sp, Call("range", evaluation));

        return Disp(Seq(
            Exists, Sp, context, Colon, Sp,
            Arrow(Seq(Operatorname, Grp(F.Id("Fin")), Open, D(2), Close),
                Call("RankOneContext", D(1))), Comma, RowBreak, Grp(),
            Grp(Seq(Forall, Sp, l, Comma, Sp, k, Comma, Sp, j, Comma, Sp, r, Comma, Sp, overlap)),
            Sp, Land, Sp, readout, Sp, Land, Sp,
            Exists, Sp, evaluation, Colon, Sp,
            Arrow(F.Id("Unit"), Arrow(F.Id("Unit"), F.Id("Bool"))), Comma, Sp,
            Exists, Sp, twist, Colon, Sp, Arrow(F.Id("Bool"), F.Id("Bool")), Comma, RowBreak, Grp(),
            Grp(Seq(Forall, Sp, y, Comma, Sp, Call("Neq", Call("twist", y), y))),
            Sp, Land, Sp, diagonal, Dot));
    }
}
