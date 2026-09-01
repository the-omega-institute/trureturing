using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class FourTypedCompletionHierarchyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/FourTypedCompletionHierarchy."
            + "four_typed_completion_hierarchy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target, state-family, algebra, and uniform completion remain distinct typed claims.",
        H("Four Typed Completion Modes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-four-type-completion-hierarchy"),
                DeclarationHandle.Create(Declaration),
                H("The four completion modes form a strict typed hierarchy"),
                StatementSource.FromAuthor(HierarchyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary scalar and Hilbert carriers K and H, with RCLike K, a "
                            + "normed additive commutative group H, an inner-product structure, "
                            + "orthogonally complemented stages V, a state family T, and a target "
                            + "x, uniform projection convergence implies convergence of the "
                            + "canonical family residual. If x belongs to T, family convergence "
                            + "then implies target convergence.")),
                    Paragraph(Text(
                        "A constant zero tower on the real line resolves target zero but not the "
                            + "two-point family. A constant one-dimensional complex subspace "
                            + "resolves its displayed nonzero member family while every stage "
                            + "remains proper, so uniform convergence fails.")),
                    Paragraph(Text(
                        "For algebra completion, the two-address clock-and-shift algebra is the "
                            + "full matrix algebra and contains the displayed off-diagonal "
                            + "observable. The state constructed from that observable nevertheless "
                            + "fails target, singleton-family, and uniform projection convergence "
                            + "for the constant zero tower.")),
                    Paragraph(Text(
                        "Conversely, the constant top tower resolves the displayed matrix-derived "
                            + "state, its singleton family, and the uniform ball. The finite "
                            + "prime-diagonal operational algebra is still proper and omits the "
                            + "same constructed off-diagonal observable. Thus every completion "
                            + "claim in the statement remains attached to its target, family, "
                            + "operator algebra, or uniform-ball object."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Stage(Formula stages, Formula index) => Apply(stages, index);

    private static Formula Perpendicular(Formula space) => Seq(space, Caret, Grp(Perp));

    private static Formula Projection(Formula space, Formula vector) =>
        Apply(Call("P", space), vector);

    private static Formula ResidualNorm(
        Formula stages,
        Formula index,
        Formula vector) =>
        new Formula.Norm(Projection(Perpendicular(Stage(stages, index)), vector));

    private static Formula FamilyResidual(
        Formula stages,
        Formula index,
        Formula family,
        Formula member) =>
        Seq(
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(member, InMacro, Sp, family), Sp,
            ResidualNorm(stages, index, member));

    private static Formula UniformNorm(Formula stages, Formula index) =>
        new Formula.Norm(Seq(
            F.Id("I"), Sp, Minus, Sp, Call("P", Stage(stages, index))));

    private static Formula LimitZero(Formula index, Formula expression) =>
        Seq(Call("lim", index, Infty, expression), Sp, Eq, Sp, D(0));

    private static Formula Target(Formula stages, Formula target) =>
        Call("Target", stages, target);

    private static Formula Family(Formula stages, Formula family) =>
        Call("StateFamily", stages, family);

    private static Formula Uniform(Formula stages) => Call("UniformBall", stages);

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.AddRange([Open, clauses[index], Close]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Definition(Formula name, Formula type, Formula value) =>
        Seq(name, Colon, Sp, type, Sp, Colon, Eq, Sp, value);

    private static Formula LetClause(Formula[] definitions, Formula body)
    {
        var items = new List<Formula>
        {
            Open, F.Text, Grp(F.Id("let")), Sp,
        };
        for (var index = 0; index < definitions.Length; index++)
        {
            if (index > 0) items.AddRange([Semi, Sp]);
            items.Add(definitions[index]);
        }
        items.AddRange([Semi, Sp, body, Close]);
        return Seq([.. items]);
    }

    private static Formula PairVector(Formula first, Formula second) =>
        Call("toLp2", first, second);

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        Call("entry", matrix, row, column);

    private static Formula HierarchyFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula stages = F.Id("V");
        Formula family = F.Id("T");
        Formula target = F.Id("x");
        Formula member = F.Id("y");
        Formula index = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = F.Id("Type");
        Formula genericSubmodule = Call("Submodule", scalar, space);
        Formula complexPlane = Call("EuclideanSpace", complexes, Call("Fin", D(2)));
        Formula realSubmodule = Call("Submodule", reals, reals);
        Formula complexSubmodule = Call("Submodule", complexes, complexPlane);
        Formula realSet = Call("Set", reals);
        Formula complexSet = Call("Set", complexPlane);
        Formula zeroOne = Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace);

        Formula targetDefinition = Seq(
            Target(stages, target), Sp, Colon, Eq, Sp,
            LimitZero(index, ResidualNorm(stages, index, target)));
        Formula familyDefinition = Seq(
            Family(stages, family), Sp, Colon, Eq, Sp,
            LimitZero(index, FamilyResidual(stages, index, family, member)));
        Formula uniformDefinition = Seq(
            Uniform(stages), Sp, Colon, Eq, Sp,
            LimitZero(index, UniformNorm(stages, index)));

        Formula forward = And(
            Seq(Uniform(stages), Sp, Rightarrow, Sp, Family(stages, family)),
            Seq(
                target, InMacro, Sp, family, Sp, Rightarrow, Sp,
                Family(stages, family), Sp, Rightarrow, Sp, Target(stages, target)));

        Formula v0 = F.Id("V0");
        Formula t0 = F.Id("T0");
        Formula targetNotFamily = LetClause(
            [
                Definition(v0, Arrow(naturals, realSubmodule),
                    Seq(index, Sp, Mapsto, Sp, F.Id("bot"))),
                Definition(t0, realSet, zeroOne),
            ],
            And(Target(v0, D(0)), Seq(Neg, Sp, Family(v0, t0))));

        Formula e0 = F.Id("e0");
        Formula w = F.Id("W");
        Formula v1 = F.Id("V1");
        Formula t1 = F.Id("T1");
        Formula familyNotUniform = LetClause(
            [
                Definition(e0, complexPlane, PairVector(D(1), D(0))),
                Definition(w, complexSubmodule, Seq(complexes, Sp, Cdot, Sp, e0)),
                Definition(v1, Arrow(naturals, complexSubmodule),
                    Seq(index, Sp, Mapsto, Sp, w)),
                Definition(t1, complexSet, Seq(OpenBrace, e0, CloseBrace)),
            ],
            And(Family(v1, t1), Seq(Neg, Sp, Uniform(v1))));

        Formula a2 = F.Id("A2");
        Formula s2 = F.Id("s2");
        Formula v2 = F.Id("V2");
        Formula t2 = F.Id("T2");
        Formula zmodTwo = Call("ZMod", D(2));
        Formula zmodMatrix = Call("Matrix", zmodTwo, zmodTwo, complexes);
        Formula fullAlgebraWithoutResolution = LetClause(
            [
                Definition(a2, zmodMatrix, Call("single", D(0), D(1), D(1))),
                Definition(s2, complexPlane,
                    PairVector(Entry(a2, D(0), D(0)), Entry(a2, D(0), D(1)))),
                Definition(v2, Arrow(naturals, complexSubmodule),
                    Seq(index, Sp, Mapsto, Sp, F.Id("bot"))),
                Definition(t2, complexSet, Seq(OpenBrace, s2, CloseBrace)),
            ],
            And(
                Seq(a2, Sp, InMacro, Sp, Call("windowGeneratedAlgebra", D(2))),
                Seq(Call("windowGeneratedAlgebra", D(2)), Sp, Eq, Sp, F.Id("top")),
                Seq(s2, Sp, Eq, Sp, PairVector(D(0), D(1))),
                Seq(Neg, Sp, Target(v2, s2)),
                Seq(Neg, Sp, Family(v2, t2)),
                Seq(Neg, Sp, Uniform(v2))));

        Formula a3 = F.Id("A3");
        Formula s3 = F.Id("s3");
        Formula v3 = F.Id("V3");
        Formula t3 = F.Id("T3");
        Formula finTwo = Call("Fin", D(2));
        Formula finMatrix = Call("Matrix", finTwo, finTwo, complexes);
        Formula resolvedWithProperAlgebra = LetClause(
            [
                Definition(a3, finMatrix, Call("single", D(1), D(0), D(1))),
                Definition(s3, complexPlane,
                    PairVector(Entry(a3, D(1), D(0)), Entry(a3, D(1), D(1)))),
                Definition(v3, Arrow(naturals, complexSubmodule),
                    Seq(index, Sp, Mapsto, Sp, F.Id("top"))),
                Definition(t3, complexSet, Seq(OpenBrace, s3, CloseBrace)),
            ],
            And(
                Uniform(v3),
                Family(v3, t3),
                Target(v3, s3),
                Seq(Call("primeDiagonalAlgebra", D(2), Emptyset), Sp, Neq, Sp, F.Id("top")),
                Seq(
                    Neg, Sp, Open, a3, Sp, InMacro, Sp,
                    Call("primeDiagonalAlgebra", D(2), Emptyset), Close)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", space), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, space), Comma,
            RowBreak, Grp(),
            stages, Colon, Sp, Arrow(naturals, genericSubmodule), Comma, Sp,
            Open, Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            Call("HasOrthogonalProjection", Stage(stages, index)), Close, Comma,
            RowBreak, Grp(),
            family, Colon, Sp, Call("Set", space), Comma, Sp,
            target, Colon, Sp, space, Comma,
            RowBreak, Grp(),
            forward, Sp, Land, RowBreak, Grp(),
            targetNotFamily, Sp, Land, RowBreak, Grp(),
            familyNotUniform, Sp, Land, RowBreak, Grp(),
            fullAlgebraWithoutResolution, Sp, Land, RowBreak, Grp(),
            resolvedWithProperAlgebra, Dot,
            RowBreak, Grp(),
            F.Text, Grp(F.Id("where")), Sp,
            targetDefinition, Semi, Sp,
            familyDefinition, Semi, Sp,
            uniformDefinition,
            End, Grp(F.Id("gathered"))));
    }
}
