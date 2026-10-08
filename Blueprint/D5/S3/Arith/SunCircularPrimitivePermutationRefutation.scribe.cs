using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SunCircularPrimitivePermutationRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/SunCircularPrimitivePermutationRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over the field of eleven elements, offset two forces the vertices two and nine "
            + "to share their two cyclic neighbours. A cycle of length ten cannot contain "
            + "this configuration.",
        H("Sun's Circular Primitive Permutation Conjecture Is False"),
        Blocks(
            Node("circular-primitive-claim", "Circular primitive permutation", "claim",
                ClaimFormula(),
                "Zhi-Wei Sun, Some new problems in additive combinatorics, arXiv:1309.1679, "
                    + "Conjecture 3.8, asserts this property for every finite field of order "
                    + "greater than seven and every offset. The equivalence lists each nonzero "
                    + "element once. The rotation advances one position and takes the last "
                    + "position to the first. A root of exact order q minus one generates the "
                    + "multiplicative group of a field of order q.",
                DescribeRole.Definition),
            Node("twin-neighbours", "The two-neighbour obstruction",
                "twin_neighbour_obstruction", TwinFormula(),
                "Write p and r for the positions of two distinct vertices. Each vertex has "
                    + "two distinct cyclic neighbours. If both pairs lie in a common set of "
                    + "at most two elements, the neighbour pairs coincide. Matching successors "
                    + "or predecessors forces p to equal r. The remaining matching interchanges "
                    + "predecessors and successors and would force the cycle length to divide "
                    + "four. Both alternatives are impossible when the length is greater than four.",
                DescribeRole.Theorem),
            Node("sun-conjecture-refuted", "Failure over the field of eleven elements",
                "result", Disp(new Formula.Not(F.Id("claim"))),
                "In the field of eleven elements, an element outside the set containing "
                    + "two, six, seven and eight is zero or has second or fifth power one, "
                    + "so it cannot have order ten. Distinct cyclic positions have distinct "
                    + "vertices. With offset two, the neighbours of "
                    + "both two and nine must therefore lie in the set containing three and "
                    + "eight. Commutativity gives the same restriction for predecessors as "
                    + "for successors. The two-neighbour obstruction excludes the required "
                    + "circular permutation of the ten nonzero elements.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sun-2013-circular-primitive-permutation-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);

    private static Formula Equivalence(Formula left, Formula right) =>
        Seq(left, Sp, Equiv, Sp, right);

    private static Formula Nonzero(Formula field) =>
        Seq(OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp, field, Sp, Bar, Sp,
            Rel(F.Id("x"), FormulaRelationOperator.NotEqual, D(0)), Sp, CloseBrace, Sp);

    private static Formula ClaimFormula()
    {
        var field = F.Id("F"); var a = F.Id("a"); var i = F.Id("i");
        var q = Call("FintypeCard", field); var size = Sub(q, D(1));
        var product = new Formula.Binary(Call("val", Call("e", i)),
            FormulaBinaryOperator.Multiply,
            Call("val", Call("e", Call("finRotate", size, i))));
        var primitive = Call("IsPrimitiveRoot",
            new Formula.Binary(a, FormulaBinaryOperator.Add, product), size);
        var assertion = All("F", new Formula.NamedConstant(FormulaIdentifier.Create("Type")),
            Seq(Instance("Field", field), Instance("Fintype", field),
                Instance("DecidableEq", field),
                Imp(Rel(D(7), FormulaRelationOperator.LessThan, q),
                    All("a", field, Exists("e", Equivalence(Call("Fin", size), Nonzero(field)),
                        All("i", Call("Fin", size), primitive))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, assertion));
    }

    private static Formula Neighbours(Formula m, Formula e, Formula x, Formula s)
    {
        var position = Call("symm", e, x); var rotation = Call("finRotate", m);
        return And(
            Rel(Call("e", Call("finRotate", m, position)), FormulaRelationOperator.MemberOf, s),
            Rel(Call("e", Call("symm", rotation, position)), FormulaRelationOperator.MemberOf, s));
    }

    private static Formula TwinFormula()
    {
        var type = F.Id("A"); var m = F.Id("m"); var e = F.Id("e");
        var u = F.Id("u"); var w = F.Id("w"); var s = F.Id("S");
        var assumptions = And(Rel(D(4), FormulaRelationOperator.LessThan, m),
            And(Rel(u, FormulaRelationOperator.NotEqual, w),
                And(Rel(Call("card", s), FormulaRelationOperator.LessThanOrEqual, D(2)),
                    And(Neighbours(m, e, u, s), Neighbours(m, e, w, s)))));
        return Disp(All("A", new Formula.NamedConstant(FormulaIdentifier.Create("Type")),
            Seq(Instance("DecidableEq", type),
                All("m", new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
                    All("e", Equivalence(Call("Fin", m), type),
                        All("u", type, All("w", type, All("S", Call("Finset", type),
                            Imp(assumptions, new Formula.NamedConstant(
                                FormulaIdentifier.Create("False")))))))))));
    }
}
