using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class DetectedOrderTwoHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mod-two functional detects a nonzero order-two class in integral ModuleCat homology.",
        H("Detecting an integral homology class of order two"),
        Blocks(
            Node("cycle-class-map", "cycleClassMap", "The class map into actual categorical homology",
                "For every short complex S of integer modules, cycleClassMap S is the integer-linear map "
                + "from the concrete kernel of S.g to S.homology. It first takes the quotient by the range "
                + "of S.moduleCatToCycles and then applies the inverse of Mathlib's moduleCatHomologyIso. "
                + "Thus its codomain is the existing ShortComplex homology object, not an unrelated quotient.",
                DescribeRole.Definition),
            Node("class-zero-iff-boundary", "cycleClassMap_eq_zero_iff", "A class vanishes exactly when it bounds",
                "For every S : ShortComplex (ModuleCat Z) and z in LinearMap.ker S.g.hom, "
                + "cycleClassMap S z = 0 if and only if there exists c in S.X1 with S.f c = z. "
                + "The proof uses the exact ModuleCat homology isomorphism and quotient-zero criterion.",
                DescribeRole.Theorem),
            Node("detected-order-two", "detected_order_two", "A detected cycle whose double bounds",
                "For every short complex S of integer modules, every z in the kernel of S.g, every c in S.X1 "
                + "with S.f c = 2 times z, and every integer-linear map phi from S.X2 to ZMod 2 which is "
                + "zero on S.f b for all b in S.X1 and is nonzero on z, the actual class cycleClassMap S z "
                + "is nonzero and its double is zero. These hypotheses impose no finiteness or exactness "
                + "assumptions on the other classes. The eleven-vertex independence-complex seed consumes "
                + "this construction; no singular-homology comparison is part of this theorem.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);

    private static Formula Statement(string declaration)
    {
        Formula s = F.Id("S"), z = F.Id("z"), c = F.Id("c"), phi = F.Id("phi"), b = F.Id("b");
        Formula ker = Call("ker", Call("g", s));
        Formula x = Call("middleModule", s), y = Call("sourceModule", s);
        Formula cls = Call("cycleClassMap", s, z);
        Formula bounds = Seq(Exists, Sp, c, Colon, Sp, y, Comma, Sp, Call("f", s, c), Eq, z);
        Formula body = declaration switch
        {
            "cycleClassMap" => Seq(Call("cycleClassMap", s), Colon, Sp,
                Call("integerLinearMap", ker, Call("homology", s))),
            "cycleClassMap_eq_zero_iff" => All("z", ker,
                Seq(cls, Eq, D(0), Sp, Iff, Sp, bounds)),
            "detected_order_two" => All("z", ker, All("c", y,
                All("phi", Call("integerLinearMap", x, Call("ZMod", D(2))),
                Seq(Call("f", s, c), Eq, D(2), Cdot, Sp, z, Sp, Rightarrow, Sp,
                    Open, All("b", y, Seq(Call("apply", phi, Call("f", s, b)), Eq, D(0))), Close,
                    Sp, Rightarrow, Sp, Call("apply", phi, z), Sp, Neq, Sp, D(0),
                    Sp, Rightarrow, Sp, cls, Sp, Neq, Sp, D(0), Sp, Land, Sp,
                    D(2), Cdot, Sp, cls, Eq, D(0))))),
            _ => throw new System.InvalidOperationException(declaration)
        };
        return Disp(All("S", Call("ShortComplex", Call("ModuleCat", Seq(Mathbb, Grp(F.Id("Z"))))), body));
    }

}
