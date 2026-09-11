using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PatternAvoidance;

internal sealed class ArcherBourneDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.";
    private static readonly LibraryNoteRef ArcherBourne =
        LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permutations avoiding 312 and 321 are exactly the direct sums of cyclic rotations indexed by compositions, and the cube criterion gives the corresponding counting identity.",
        H("Archer-Bourne Decomposition"),
        Blocks(
            Node(
                "pattern-312",
                "pattern312",
                "The pattern 312",
                PatternFormula(Pattern312(), D(2), D(0), D(1)),
                "The zero-based values two, zero, one define the permutation pattern 312.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(ArcherBourne)),
            Node(
                "pattern-321",
                "pattern321",
                "The pattern 321",
                PatternFormula(Pattern321(), D(2), D(1), D(0)),
                "The zero-based values two, one, zero define the permutation pattern 321.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(ArcherBourne)),
            Node(
                "avoids-312",
                "Avoids312",
                "Avoidance of 312",
                AvoidanceDefinition(D(3, 1, 2), Pattern312()),
                "This is the negation of the generic pattern-containment predicate at the permutation 312.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(ArcherBourne)),
            Node(
                "avoids-321",
                "Avoids321",
                "Avoidance of 321",
                AvoidanceDefinition(D(3, 2, 1), Pattern321()),
                "This is the negation of the generic pattern-containment predicate at the permutation 321.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(ArcherBourne)),
            Node(
                "rotation-sum-permutation-avoids-312-321",
                "rotationSumPerm_avoids_312_321",
                "Positive rotation sums avoid both patterns",
                RotationSumAvoidanceFormula(),
                "A list of positive block sizes determines a direct sum of cyclic rotations. Archer and Bourne's Lemma 3.1 gives the avoidance direction of this characterization.",
                DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(ArcherBourne)),
            Node(
                "rotation-sum-composition",
                "rotationSumComposition",
                "Rotation sum indexed by a composition",
                RotationSumCompositionFormula(),
                "The sum equation carried by a Mathlib composition transports the list-level rotation sum to a permutation of the required finite interval.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(ArcherBourne)),
            Node(
                "rotation-sum-composition-avoids-312-321",
                "rotationSumComposition_avoids_312_321",
                "Every composition gives an avoider",
                CompositionAvoidanceFormula(),
                "Every block of a composition is positive, so the associated rotation sum avoids both 312 and 321.",
                DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(ArcherBourne)),
            Node(
                "avoids-312-321-iff-rotation-sum-composition",
                "avoids_312_321_iff_exists_rotationSumComposition",
                "Archer-Bourne decomposition",
                DecompositionFormula(),
                "A permutation avoids 312 and 321 exactly when it is the direct sum of the cyclic rotations determined by a composition of its size. This is Archer and Bourne's Lemma 3.1.",
                DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(ArcherBourne)),
            Node(
                "rotation-sum-composition-injective",
                "rotationSumComposition_injective",
                "Uniqueness of the composition",
                InjectivityFormula(),
                "Descent positions recover all composition boundaries, so equal rotation sums have equal compositions. Together with the decomposition theorem, this is the bijection identified after Lemma 3.1.",
                DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(ArcherBourne)),
            Node(
                "rotation-sum-composition-cube-avoids-2143",
                "rotationSumComposition_cube_avoids_2143_iff",
                "Cube avoidance criterion for compositions",
                CubeCriterionFormula(),
                "Transporting the list-level cube criterion to Mathlib compositions shows that at most one part may differ from one and three.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(ArcherBourne)),
            Node(
                "card-avoids-312-321-cube-2143-eq-compositions",
                "card_avoids_312_321_cube_2143_eq_compositions",
                "The Archer-Bourne counting equality",
                CountingFormula(),
                "The decomposition and its uniqueness identify the 312/321 avoiders with compositions. The frozen cube criterion restricts this bijection on both sides to exactly the displayed exceptional-part condition.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(ArcherBourne),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("archer-bourne-cube-2143-count"),
                    ResolutionKind.Proved))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Words/Patterns/DerangementRatioNonconvergence")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance")),
        ]));

    private static DocumentBlock.Describe Node(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            provenance,
            Blocks(Paragraph(Text(explanation))),
            role,
            resolution);

    private static Formula PatternFormula(Formula pattern, Formula a, Formula b, Formula c) =>
        Disp(Seq(
            pattern, Sp, Colon, Sp, Perm(D(3)), Sp, Colon, Eq, Sp,
            Bracket(Seq(a, Comma, Sp, b, Comma, Sp, c)), Dot));

    private static Formula AvoidanceDefinition(Formula patternName, Formula pattern)
    {
        Formula n = F.Id("n");
        Formula pi = Pi;
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, pi, Sp, InMacro, Sp, Perm(n), Comma, Sp,
            Avoids(patternName, pi), Sp, Colon, Eq, Sp,
            Neg, Sp, Call("Contains", pattern, pi), Dot));
    }

    private static Formula RotationSumAvoidanceFormula()
    {
        Formula d = F.Id("d");
        Formula i = F.Id("i");
        Formula positivity = Seq(
            Forall, Sp, i, Sp, InMacro, Sp, FinIndices(d), Comma, Sp,
            D(0), Sp, Lt, Sp, Part(d, i));
        Formula rotation = RotationSumPerm(d);
        return Disp(Seq(
            Forall, Sp, d, Sp, InMacro, Sp, Call("List", Naturals()), Comma, Sp,
            Parenthesized(positivity), Sp, Rightarrow, Sp,
            Parenthesized(Seq(
                Avoids(D(3, 1, 2), rotation), Sp, Land, Sp,
                Avoids(D(3, 2, 1), rotation))), Dot));
    }

    private static Formula RotationSumCompositionFormula()
    {
        Formula n = F.Id("n");
        Formula c = F.Id("c");
        Formula equation = Seq(SumParts(c), Sp, Eq, Sp, n);
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, c, Sp, InMacro, Sp, Composition(n), Comma, Sp,
            RotationSumComposition(c), Colon, Sp, Perm(n), Sp, Colon, Eq, Sp,
            new Formula.Subscript(Call("transport", RotationSumPerm(BlocksOf(c))), equation),
            Dot));
    }

    private static Formula CompositionAvoidanceFormula()
    {
        Formula n = F.Id("n");
        Formula c = F.Id("c");
        Formula rotation = RotationSumComposition(c);
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, c, Sp, InMacro, Sp, Composition(n), Comma, Sp,
            Avoids(D(3, 1, 2), rotation), Sp, Land, Sp,
            Avoids(D(3, 2, 1), rotation), Dot));
    }

    private static Formula DecompositionFormula()
    {
        Formula n = F.Id("n");
        Formula pi = Pi;
        Formula c = F.Id("c");
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, pi, Sp, InMacro, Sp, Perm(n), Comma, Sp,
            Parenthesized(Seq(
                Avoids(D(3, 1, 2), pi), Sp, Land, Sp,
                Avoids(D(3, 2, 1), pi))),
            Sp, Leftrightarrow, Sp,
            Parenthesized(Seq(
                Exists, Sp, c, Sp, InMacro, Sp, Composition(n), Comma, Sp,
                pi, Sp, Eq, Sp, RotationSumComposition(c))), Dot));
    }

    private static Formula InjectivityFormula()
    {
        Formula n = F.Id("n");
        Formula c = F.Id("c");
        Formula e = F.Id("e");
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, c, Comma, Sp, e, Sp, InMacro, Sp, Composition(n), Comma, Sp,
            RotationSumComposition(c), Sp, Eq, Sp, RotationSumComposition(e),
            Sp, Rightarrow, Sp, c, Sp, Eq, Sp, e, Dot));
    }

    private static Formula CubeCriterionFormula()
    {
        Formula n = F.Id("n");
        Formula c = F.Id("c");
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, c, Sp, InMacro, Sp, Composition(n), Comma, Sp,
            Neg, Sp, Contains2143(new Formula.Power(RotationSumComposition(c), D(3))),
            Sp, Leftrightarrow, Sp,
            Call("card", ExceptionalIndices(c)), Sp, Leq, Sp, D(1), Dot));
    }

    private static Formula CountingFormula()
    {
        Formula n = F.Id("n");
        Formula pi = Pi;
        Formula c = F.Id("c");
        Formula permutations = SetOf(pi, Perm(n), Seq(
            Avoids(D(3, 1, 2), pi), Sp, Land, Sp,
            Avoids(D(3, 2, 1), pi), Sp, Land, Sp,
            Neg, Sp, Contains2143(new Formula.Power(pi, D(3)))));
        Formula compositions = SetOf(c, Composition(n), Seq(
            Call("card", ExceptionalIndices(c)), Sp, Leq, Sp, D(1)));
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Call("card", permutations), Sp, Eq, Sp,
            Call("card", compositions), Dot));
    }

    private static Formula ExceptionalIndices(Formula c)
    {
        Formula i = F.Id("i");
        Formula part = Part(BlocksOf(c), i);
        return SetOf(i, FinIndices(BlocksOf(c)), Seq(
            part, Sp, Neq, Sp, D(1), Sp, Land, Sp,
            part, Sp, Neq, Sp, D(3)));
    }

    private static Formula SetOf(Formula variable, Formula domain, Formula condition) =>
        Seq(OpenBrace,
            variable, Sp, InMacro, Sp, domain, Sp, Colon, Sp, condition,
            CloseBrace);

    private static Formula SumParts(Formula c)
    {
        Formula i = F.Id("i");
        return Seq(
            Sum, Underscore, Grp(i, Sp, InMacro, Sp, FinIndices(BlocksOf(c))), Sp,
            Part(BlocksOf(c), i));
    }

    private static Formula Pattern312() =>
        new Formula.Subscript(F.Id("p"), D(3, 1, 2));

    private static Formula Pattern321() =>
        new Formula.Subscript(F.Id("p"), D(3, 2, 1));

    private static Formula Avoids(Formula pattern, Formula pi) =>
        new Formula.Apply(new Formula.Subscript(F.Id("Avoids"), pattern), [pi]);

    private static Formula Contains2143(Formula value) =>
        new Formula.Apply(new Formula.Subscript(F.Id("Contains"), D(2, 1, 4, 3)), [value]);

    private static Formula Perm(Formula n) => Call("Perm", Call("Fin", n));

    private static Formula Composition(Formula n) => Call("Composition", n);

    private static Formula RotationSumPerm(Formula d) => Call("rotationSumPerm", d);

    private static Formula RotationSumComposition(Formula c) =>
        Call("rotationSumComposition", c);

    private static Formula BlocksOf(Formula c) => Call("blocks", c);

    private static Formula FinIndices(Formula d) => Call("Fin", Call("length", d));

    private static Formula Part(Formula d, Formula i) => new Formula.Subscript(d, i);

    private static Formula Bracket(Formula value) => Seq(OpenBracket, value, CloseBracket);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
