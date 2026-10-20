using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class FaceMagicModuleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.";
    private const string SourceQuestion =
        "What is the structure of the R-module U_n(R) of face magic hypercubes of dimension n over R when the characteristic is even and positive?";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/bhargava2026facemagic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-ring coordinates classify unrestricted face-magic hypercubes.",
        H("The face-magic hypercube module"),
        Blocks(
            Describe.Lean(DescribeId.Create("face-magic-definition"),
                DeclarationHandle.Create(Prefix + "FaceMagic"),
                H("Common face sums"), StatementSource.FromAuthor(DefinitionFormula(false)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "FaceMagic n f means that there is one C in the ring such that every "
                    + "two-coordinate face S, S∪{i}, S∪{j}, S∪{i,j}, with distinct i and j outside S, "
                    + "has sum C. The carrier is the actual function space of arrays admitting "
                    + "such a C; C is not stored in the carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("face-magic-module"),
                DeclarationHandle.Create(Prefix + "faceMagicModule"),
                H("The face-magic submodule"), StatementSource.FromAuthor(DefinitionFormula(true)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The arrays satisfying the common-face condition form an R-submodule by "
                    + "adding witnesses and scaling a witness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("face-magic-module-structure"),
                DeclarationHandle.Create(Prefix + "face_magic_module_structure"),
                H("All-ring coordinate classification"), StatementSource.FromAuthor(StructureFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The source question is: " + SourceQuestion + " The theorem answers it over every unital ring. In "
                    + "dimension zero evaluation at the empty subset is an R-linear equivalence "
                    + "with R. In dimension one the empty and singleton entries give an "
                    + "equivalence with R × R. For n ≥ 2, evaluation at the empty subset, at "
                    + "each singleton, and on the fixed {0,1}-face gives an equivalence with "
                    + "R × (Fin n → R) × R. The inverse is the explicit integer-coordinate "
                    + "formula: for k = |S| it is (-1)^k ((1-k)a − Σ_{i∈S} b_i + "
                    + "floor(k/2) C), interpreted by additive integer coefficients. No division "
                    + "by two is used, so zero divisors and every characteristic are included. "
                    + "The face identity follows by the parity second difference of floor(k/2), "
                    + "and the inverse law follows by strong induction on the subset cardinality. "
                    + "Bhargava Section 2, equations (4), (8), (9) and Theorem 13 supply the "
                    + "face recurrence and induction method. The empty-entry, singleton-entry "
                    + "and common-face-sum coordinates instead give an integral reconstruction, "
                    + "avoiding the invertibility of two required by the source's determinant-two coordinates."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhargava-2026-facemagic-module"),
                    ResolutionKind.Proved))),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula Product(Formula left, Formula right) =>
        Call("Prod", left, right);

    private static Formula Function(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Equiv(Formula scalar, Formula source, Formula target) =>
        Call("LinearEquiv", scalar, source, target);

    private static Formula DefinitionFormula(bool membership)
    {
        Formula ring = F.Id("R");
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula s = F.Id("S");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula c = F.Id("C");
        Formula indices = Call("Fin", n);
        Formula subsets = Call("Finset", indices);
        Formula absentI = Seq(Neg, Parenthesized(Seq(i, Sp, InMacro, Sp, s)));
        Formula absentJ = Seq(Neg, Parenthesized(Seq(j, Sp, InMacro, Sp, s)));
        Formula hypotheses = Parenthesized(Seq(
            absentI, Sp, Land, Sp, absentJ, Sp, Land, Sp, i, Sp, Neq, Sp, j));
        Formula faceSum = Seq(
            Call("f", s), Sp, Plus, Sp, Call("f", Call("insert", i, s)), Sp, Plus, Sp,
            Call("f", Call("insert", j, s)), Sp, Plus, Sp,
            Call("f", Call("insert", i, Call("insert", j, s))), Sp, Eq, Sp, c);
        Formula condition = Seq(
            Exists, Sp, c, Sp, InMacro, Sp, ring, Comma, Esc,
            Forall, Sp, s, Sp, InMacro, Sp, subsets, Comma, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, indices, Comma, Sp,
            Forall, Sp, j, Sp, InMacro, Sp, indices, Comma, Esc,
            hypotheses, Sp, Rightarrow, Sp, faceSum);
        Formula left = membership
            ? Seq(f, Sp, InMacro, Sp, Call("faceMagicModule", ring, n))
            : Call("FaceMagic", ring, n, f);
        return Disp(Seq(
            Forall, Sp, ring, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Ring", ring), Comma, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, F.Id("Nat"), Comma, Sp,
            Forall, Sp, f, Sp, InMacro, Sp, Parenthesized(Function(subsets, ring)), Comma, Esc,
            Parenthesized(left), Sp, Iff, Sp, Parenthesized(condition)));
    }

    private static Formula StructureFormula()
    {
        Formula ring = F.Id("R");
        Formula nat = F.Id("Nat");
        Formula module0 = Call("faceMagicModule", ring, D(0));
        Formula module1 = Call("faceMagicModule", ring, D(1));
        Formula moduleN = Call("faceMagicModule", ring, F.Id("n"));
        Formula finiteFunction = Function(Call("Fin", F.Id("n")), ring);
        Formula targetN = Product(ring, Product(finiteFunction, ring));
        Formula low = Parenthesized(Seq(
            Call("Nonempty", Equiv(ring, module0, ring)), Sp, Land, Sp,
            Call("Nonempty", Equiv(ring, module1, Product(ring, ring)))));
        Formula high = Seq(
            Forall, Sp, F.Id("n"), Sp, InMacro, Sp, nat, Comma, Esc,
            Parenthesized(Seq(
                D(2), Sp, Leq, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                Call("Nonempty", Equiv(ring, moduleN, targetN)))));
        return Disp(Seq(
            Forall, Sp, ring, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Ring", ring), Comma, Esc,
            low, Sp, Land, Sp, high));
    }
}
