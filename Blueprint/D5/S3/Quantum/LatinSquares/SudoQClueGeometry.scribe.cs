using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.LatinSquares;

internal sealed class SudoQClueGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/LatinSquares/SudoQClueGeometry.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/paczosetal2021sudoq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clue-fixing isometries force a repeated ray in every SudoQ unit.",
        H("Clue geometry of four by four SudoQ"),
        Blocks(
            Paragraph(Text("Vectors belong to EuclideanSpace over Complex with four coordinates. "
                + "Rows and columns use zero-based Fin indices. A clue fixes its literal vector; "
                + "equality of solutions compares each entry up to a unit complex phase. "
                + "Four orthonormal vectors in this space form an orthonormal basis.")),
            Node("block", "Block coordinates", "blockCell", BlockFormula(),
                "For block b and offset k, the cell has coordinates 2*b.1+k.1 and "
                + "2*b.2+k.2. Each coordinate uses Mathlib's finProdFinEquiv on the "
                + "corresponding block index and offset.", false),
            Describe.Lean(DescribeId.Create("sudoq-geometry-sudoq"),
                DeclarationHandle.Create(Prefix + "IsSudoQ"), H("SudoQ constraints"),
                StatementSource.FromAuthor(Disp(SudoQFormula())),
                AssessedProvenance.FromLiterature(Source), Blocks(SudoQQuotation()),
                DescribeRole.Definition),
            Node("solution", "A completion with prescribed clues", "IsSolution", SolutionFormula(),
                "Definition 8, page 3: “A quantum grid is a SudoQ grid whose some entries "
                + "can be blank.” Definition 9, page 3: “A quantum grid is called solvable "
                + "if it has at least one solution.” C is precisely the set of nonblank "
                + "cells, as in the six-clue example after Definition 9. v prescribes their "
                + "vectors, and G is a completion. Values of v outside C are unrestricted.", true),
            Node("rays", "Entrywise equality as rays", "SameRays", RaysFormula(),
                "Definition 5, page 2: “The cardinality c of a QLS is the number of its "
                + "vectors distinct up to a global phase.” Each entry may have its own "
                + "unit phase z. This is the ray convention used when comparing solutions.", true),
            Node("unique", "Unique solvability", "UniquelySolvable", UniqueFormula(),
                "Definition 10, page 3: “A quantum grid is called uniquely solvable if it "
                + "has a unique solution.” The existential quantifier requires a completion; "
                + "every other completion agrees with it as rays. It does not require "
                + "literal equality of phase representatives.", true),
            Node("ray", "Two vectors on the same normalized ray", "RayEq", RayFormula(),
                "Definition 5, page 2: “The cardinality c of a QLS is the number of its "
                + "vectors distinct up to a global phase.” RayEq makes the unit-phase "
                + "relation explicit for a single pair of vectors.", true),
            Node("repeated", "A ray occurring once in every unit", "HasRepeatedRay", RepeatedFormula(),
                "The ray of w occurs exactly once in every row, column and block. "
                + "The uniqueness quantifiers range over all four positions of each unit.", false),
            Theorem("symmetry", "Symmetry of ray equality", "symm",
                All("x", Vectors(), All("y", Vectors(), Imp(Ray(X, Y), Ray(Y, X)))),
                "Inverting the unit phase reverses ray equality."),
            Theorem("transitivity", "Transitivity of ray equality", "trans",
                All("x", Vectors(), All("y", Vectors(), All("z", Vectors(),
                    Imp(Ray(X, Y), Imp(Ray(Y, Z), Ray(X, Z)))))),
                "Multiplying the unit phases composes ray equality."),
            Theorem("scalar", "A scalar between unit vectors is a unit phase", "rayEq_of_smul",
                All("x", Vectors(), All("y", Vectors(),
                    Imp(Unit(X), Imp(Unit(Y), Imp(Some("z", ComplexType(),
                        Eqn(Y, Smul(Z, X))), Ray(X, Y)))))),
                "Equality of the norms forces the scalar to have norm one."),
            Theorem("orthogonal", "An orthogonal vector is a different ray", "not_rayEq_of_orthogonal",
                All("x", Vectors(), All("y", Vectors(),
                    Imp(Unit(X), Imp(Eqn(Inner(X, Y), D(0)), new Formula.Not(Ray(X, Y)))))),
                "A unit vector cannot be orthogonal to a unit-phase multiple of itself."),
            Theorem("reflexivity", "Reflexivity of ray equality", "refl",
                All("x", Vectors(), Ray(X, X)), "The phase one fixes every vector."),
            Theorem("norm", "Ray equality preserves norm", "norm",
                All("x", Vectors(), All("y", Vectors(),
                    Imp(Ray(X, Y), Eqn(Norm(Y), Norm(X))))),
                "Multiplication by a unit complex phase preserves norm."),
            Theorem("left", "Orthogonality is unchanged in the left ray", "inner_left_iff",
                All("x", Vectors(), All("u", Vectors(), All("y", Vectors(),
                    Imp(Ray(X, U), IffTo(Eqn(Inner(U, Y), D(0)), Eqn(Inner(X, Y), D(0))))))),
                "Conjugate linearity and the nonzero "
                + "unit phase preserve a zero inner product."),
            Theorem("right", "Orthogonality is unchanged in the right ray", "inner_right_iff",
                All("x", Vectors(), All("y", Vectors(), All("u", Vectors(),
                    Imp(Ray(Y, U), IffTo(Eqn(Inner(X, U), D(0)), Eqn(Inner(X, Y), D(0))))))),
                "Linearity and the nonzero unit phase "
                + "preserve a zero inner product."),
            Theorem("geometry", "Unique solvability would force a repeated ray", "unique_implies_repeated_ray",
                GeometryFormula(),
                "Let S be the complex span of the clue vectors. At most three clues "
                + "make S a proper subspace. Reflection in S fixes the clues. If all "
                + "solutions agree as rays, each entry lies in S or its orthogonal "
                + "complement. Swapping two orthogonal basis vectors in that complement "
                + "also fixes the clues and changes a ray, so the complement must be "
                + "one-dimensional. Its unit ray then occurs exactly once in every "
                + "orthonormal row, column and block."))));

    private static DocumentBlock SudoQQuotation()
    {
        var n = F.Id("N");
        var hilbert = new Formula.Subscript(Seq(Mathcal, Grp(F.Id("H"))), n);
        return Paragraph(
            Text("Definition 7, page 3: “A quantum Sudoku (SudoQ) is an "),
            Math(Seq(new Formula.Power(n, D(2)), Sp, Times, Sp, new Formula.Power(n, D(2)))),
            Text(" QLS with additional constraints that each of the disjoint blocks of size "),
            Math(n), Text(" forms an orthonormal basis.” Definition 2, page 2: “A quantum "
                + "Latin square (QLS) is an "), Math(Seq(n, Sp, Times, Sp, n)),
            Text(" array of vectors from "), Math(n),
            Text("-dimensional Hilbert space "), Math(hilbert),
            Text(", arranged in such a way that each row and column forms an orthonormal basis of "),
            Math(hilbert), Text(".” Here the Sudoku parameter is N=2, and the Latin square "
                + "dimension is four. All four rows, four columns and four disjoint blocks are quantified."));
    }

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, bool literature) => Describe.Lean(
            DescribeId.Create("sudoq-geometry-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string title, string name, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("sudoq-geometry-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula Z => F.Id("z");
    private static Formula U => F.Id("u");
    private static Formula G => F.Id("G");
    private static Formula V => F.Id("v");
    private static Formula C => F.Id("C");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("k");
    private static Formula W => F.Id("w");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula App(Formula f, params Formula[] args) =>
        Seq(f, Sp, Parenthesized(Seq([.. args.SelectMany((x, i) =>
            i == 0 ? new[] { x } : new[] { Comma, Sp, x })])));
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Some(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula ExactlyOne(string x, Formula domain, Formula body) =>
        Seq(Exists, Bang, Sp, Parenthesized(Seq(F.Id(x), Colon, Sp, domain)), Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinType(byte n) => Call("Fin", D(n));
    private static Formula Vectors() => Call("EuclideanSpace", ComplexType(), FinType(4));
    private static Formula Grids() => Arrow(FinType(4), Arrow(FinType(4), Vectors()));
    private static Formula Cells() => Seq(FinType(4), Sp, Times, Sp, FinType(4));
    private static Formula BlockIndices() => Seq(FinType(2), Sp, Times, Sp, FinType(2));
    private static Formula Values() => Arrow(Cells(), Vectors());
    private static Formula CellSets() => Call("Finset", Cells());
    private static Formula Proj(Formula a, byte i) => Seq(a, Dot, D(i));
    private static Formula Norm(Formula a) => Seq(Vert, Sp, a, Sp, Vert);
    private static Formula Unit(Formula a) => Eqn(Norm(a), D(1));
    private static Formula Inner(Formula a, Formula b) => Call("inner", ComplexType(), a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Ray(Formula a, Formula b) => Call("RayEq", a, b);
    private static Formula GridAt(Formula g, Formula i, Formula j) => App(g, i, j);
    private static Formula AtCell(Formula g, Formula c) => GridAt(g, Proj(c, 1), Proj(c, 2));
    private static Formula LambdaOf(string x, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(x), Colon, Sp, type)), Sp, Mapsto, Sp, body);

    private static Formula BlockFormula()
    {
        Formula Coordinate(byte i) => Call("finProdFinEquiv",
            Parenthesized(Seq(Proj(B, i), Comma, Sp, Proj(K, i))));
        return All("b", BlockIndices(), All("k", BlockIndices(),
            Eqn(Call("blockCell", B, K), Parenthesized(Seq(Coordinate(1), Comma, Sp, Coordinate(2))))));
    }

    private static Formula SudoQFormula() => All("G", Grids(),
        Eqn(Call("IsSudoQ", G), And(
            All("i", FinType(4), Call("Orthonormal", ComplexType(),
                LambdaOf("j", FinType(4), GridAt(G, I, J)))), And(
            All("j", FinType(4), Call("Orthonormal", ComplexType(),
                LambdaOf("i", FinType(4), GridAt(G, I, J)))),
            All("b", BlockIndices(), Call("Orthonormal", ComplexType(),
                LambdaOf("k", BlockIndices(), AtCell(G, Call("blockCell", B, K)))))))));

    private static Formula SolutionFormula() => All("C", CellSets(), All("v", Values(),
        All("G", Grids(), Eqn(Call("IsSolution", C, V, G), And(Call("IsSudoQ", G),
            All("c", Cells(), Imp(new Formula.Relation(F.Id("c"), FormulaRelationOperator.MemberOf, C),
                Eqn(AtCell(G, F.Id("c")), App(V, F.Id("c"))))))))));

    private static Formula RaysFormula() => All("G", Grids(), All("H", Grids(),
        Eqn(Call("SameRays", G, F.Id("H")), All("i", FinType(4), All("j", FinType(4),
            Some("z", ComplexType(), And(Unit(Z), Eqn(GridAt(F.Id("H"), I, J),
                Smul(Z, GridAt(G, I, J))))))))));

    private static Formula UniqueFormula() => All("C", CellSets(), All("v", Values(),
        Eqn(Call("UniquelySolvable", C, V), Some("G", Grids(),
            And(Call("IsSolution", C, V, G), All("H", Grids(),
                Imp(Call("IsSolution", C, V, F.Id("H")), Call("SameRays", G, F.Id("H")))))))));

    private static Formula RayFormula() => All("x", Vectors(), All("y", Vectors(),
        Eqn(Ray(X, Y), Some("z", ComplexType(), And(Unit(Z), Eqn(Y, Smul(Z, X)))))));

    private static Formula RepeatedFormula() => All("G", Grids(), All("w", Vectors(),
        Eqn(Call("HasRepeatedRay", G, W), And(
            All("i", FinType(4), ExactlyOne("j", FinType(4), Ray(W, GridAt(G, I, J)))), And(
            All("j", FinType(4), ExactlyOne("i", FinType(4), Ray(W, GridAt(G, I, J)))),
            All("b", BlockIndices(), ExactlyOne("k", BlockIndices(),
                Ray(W, AtCell(G, Call("blockCell", B, K))))))))));

    private static Formula GeometryFormula() => All("C", CellSets(), All("v", Values(),
        All("G", Grids(), Imp(
            new Formula.Relation(App(Q("Finset", "card"), C), FormulaRelationOperator.LessThanOrEqual, D(3)),
            Imp(Call("IsSolution", C, V, G), Imp(All("H", Grids(),
                Imp(Call("IsSolution", C, V, F.Id("H")), Call("SameRays", G, F.Id("H")))),
                Some("w", Vectors(), And(Unit(W), Call("HasRepeatedRay", G, W)))))))));
}
