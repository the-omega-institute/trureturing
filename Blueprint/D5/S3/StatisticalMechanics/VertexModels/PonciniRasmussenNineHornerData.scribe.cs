using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHo"
                +
                "rnerData.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer data for nine strands", H("Integer data for nine strands"), Blocks(
            Paragraph(Text("The 4862 diagram coordinates are embedded in Fin 8192. The " +
                "shared D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get " +
                "function reads the common Tree by parity and division by two. " +
                "D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows is the " +
                "single incoming row table, also used by " +
                "D5.S3.StatisticalMechanics.PonciniRasmussenNineEdges.incoming. " +
                "The private v0 through v58 are the integer state trees.")),

            Node("rows", Typed(N("rows"), Call(
                "D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.Tree",
                Call("List", Nat()))),
                "The literal tree contains 8192 incoming source lists. For i : Fin 8192, " +
                "D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get " +
                "D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows i.val " +
                "selects the list at i. " +
                "Its natural source indices retain their multiplicities; " +
                "sparseHamiltonian reduces them modulo 8192 with Nat.mod_lt."),

            Node("annihilatorCoefficients", Eq(N("annihilatorCoefficients"), Coefficients()),
                "These 58 integers are in highest-degree-first order."),
            Node("sparseHamiltonian", All("v", Vector(), Eq(Call("sparseHamiltonian", X("v")),
                Fn("i", Fin(D(8192)), Negate(Call("List.foldl",
                    Fn("s", IntType(), Fn("j", Nat(), Add(X("s"), At(X("v"),
                        FinMk(Call("Nat.mod", X("j"), D(8192)),
                            Call("Nat.mod_lt", X("j"), OmegaProof())))))),
                    D(0), Call("D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get",
                        N("rows"), Val(X("i")))))))),
                "The sum retains repeated source coordinates and uses the " +
                "negative Hamiltonian sign."),
            Node("hornerValue", Eq(N("hornerValue"), Call("List.foldl",
                Fn("v", Vector(), Fn("c", IntType(), Fn("i", Fin(D(8192)),
                    Add(Call("sparseHamiltonian", X("v"), X("i")),
                        If(Call("BEq.beq", Val(X("i")), D(4861)), X("c"), D(0)))))),
                ZeroVector(), N("annihilatorCoefficients"))),
                "The callback adds c only at the identity coordinate. Its " +
                "initial function is constant zero."),
            Node("state", All("k", Nat(), Eq(Call("state", X("k")), Fn("i", Fin(D(8192)),
                Call("D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get",
                    StateTree(), Val(X("i")))))),
                "The match has branches 0 through 57; every other natural number selects v58."))));
    private static Formula Coefficients() => Seq(OpenBracket, D(1), Comma, Sp, D(0), Comma, Sp,
                D(-163), Comma, Sp, D(0), Comma, Sp, D(12285), Comma, Sp, D(0), Comma, Sp,
                D(-569445), Comma, Sp, D(0), Comma, Sp, D(18215115), Comma, Sp, D(0), Comma, Sp,
                D(-427662891), Comma, Sp, D(0), Comma, Sp, D(7652877936), Comma, Sp, D(0), Comma,
                Sp, D(-106986874650), Comma, Sp, D(0), Comma, Sp, D(1188246329388), Comma, Sp, D(0)
                , Comma, Sp, D(-10605723426434), Comma, Sp, D(0), Comma, Sp, D(76659122475479),
                Comma, Sp, D(0), Comma, Sp, D(-450854928573687), Comma, Sp, D(0), Comma, Sp,
                D(2162620108980042), Comma, Sp, D(0), Comma, Sp, D(-8462844884056308), Comma, Sp,
                D(0), Comma, Sp, D(26973986982247197), Comma, Sp, D(0), Comma, Sp,
                D(-69786597194594871), Comma, Sp, D(0), Comma, Sp, D(145778728152448221), Comma, Sp
                , D(0), Comma, Sp, D(-244086630072528699), Comma, Sp, D(0), Comma, Sp,
                D(324477075047489821), Comma, Sp, D(0), Comma, Sp, D(-338328989148555271), Comma,
                Sp, D(0), Comma, Sp, D(272486148975235188), Comma, Sp, D(0), Comma, Sp,
                D(-166252500600659604), Comma, Sp, D(0), Comma, Sp, D(74962166731413102), Comma, Sp
                , D(0), Comma, Sp, D(-24185673946500264), Comma, Sp, D(0), Comma, Sp,
                D(5347591521504921), Comma, Sp, D(0), Comma, Sp, D(-762922848588417), Comma, Sp,
                D(0), Comma, Sp, D(64282035899880), Comma, Sp, D(0), Comma, Sp, D(-2771640702288),
                Comma, Sp, D(0), Comma, Sp, D(43808164416), Comma, Sp, D(0), CloseBracket);
    private static Formula StateTree() => Parenthesized(Seq(N("match"), Sp, X("k"), Sp, N("with"),
                Sp,
            Seq(Bar, Sp, D(0), Sp, Mapsto, Sp, N("v0"), Sp),
            Seq(Bar, Sp, D(1), Sp, Mapsto, Sp, N("v1"), Sp),
            Seq(Bar, Sp, D(2), Sp, Mapsto, Sp, N("v2"), Sp),
            Seq(Bar, Sp, D(3), Sp, Mapsto, Sp, N("v3"), Sp),
            Seq(Bar, Sp, D(4), Sp, Mapsto, Sp, N("v4"), Sp),
            Seq(Bar, Sp, D(5), Sp, Mapsto, Sp, N("v5"), Sp),
            Seq(Bar, Sp, D(6), Sp, Mapsto, Sp, N("v6"), Sp),
            Seq(Bar, Sp, D(7), Sp, Mapsto, Sp, N("v7"), Sp),
            Seq(Bar, Sp, D(8), Sp, Mapsto, Sp, N("v8"), Sp),
            Seq(Bar, Sp, D(9), Sp, Mapsto, Sp, N("v9"), Sp),
            Seq(Bar, Sp, D(10), Sp, Mapsto, Sp, N("v10"), Sp),
            Seq(Bar, Sp, D(11), Sp, Mapsto, Sp, N("v11"), Sp),
            Seq(Bar, Sp, D(12), Sp, Mapsto, Sp, N("v12"), Sp),
            Seq(Bar, Sp, D(13), Sp, Mapsto, Sp, N("v13"), Sp),
            Seq(Bar, Sp, D(14), Sp, Mapsto, Sp, N("v14"), Sp),
            Seq(Bar, Sp, D(15), Sp, Mapsto, Sp, N("v15"), Sp),
            Seq(Bar, Sp, D(16), Sp, Mapsto, Sp, N("v16"), Sp),
            Seq(Bar, Sp, D(17), Sp, Mapsto, Sp, N("v17"), Sp),
            Seq(Bar, Sp, D(18), Sp, Mapsto, Sp, N("v18"), Sp),
            Seq(Bar, Sp, D(19), Sp, Mapsto, Sp, N("v19"), Sp),
            Seq(Bar, Sp, D(20), Sp, Mapsto, Sp, N("v20"), Sp),
            Seq(Bar, Sp, D(21), Sp, Mapsto, Sp, N("v21"), Sp),
            Seq(Bar, Sp, D(22), Sp, Mapsto, Sp, N("v22"), Sp),
            Seq(Bar, Sp, D(23), Sp, Mapsto, Sp, N("v23"), Sp),
            Seq(Bar, Sp, D(24), Sp, Mapsto, Sp, N("v24"), Sp),
            Seq(Bar, Sp, D(25), Sp, Mapsto, Sp, N("v25"), Sp),
            Seq(Bar, Sp, D(26), Sp, Mapsto, Sp, N("v26"), Sp),
            Seq(Bar, Sp, D(27), Sp, Mapsto, Sp, N("v27"), Sp),
            Seq(Bar, Sp, D(28), Sp, Mapsto, Sp, N("v28"), Sp),
            Seq(Bar, Sp, D(29), Sp, Mapsto, Sp, N("v29"), Sp),
            Seq(Bar, Sp, D(30), Sp, Mapsto, Sp, N("v30"), Sp),
            Seq(Bar, Sp, D(31), Sp, Mapsto, Sp, N("v31"), Sp),
            Seq(Bar, Sp, D(32), Sp, Mapsto, Sp, N("v32"), Sp),
            Seq(Bar, Sp, D(33), Sp, Mapsto, Sp, N("v33"), Sp),
            Seq(Bar, Sp, D(34), Sp, Mapsto, Sp, N("v34"), Sp),
            Seq(Bar, Sp, D(35), Sp, Mapsto, Sp, N("v35"), Sp),
            Seq(Bar, Sp, D(36), Sp, Mapsto, Sp, N("v36"), Sp),
            Seq(Bar, Sp, D(37), Sp, Mapsto, Sp, N("v37"), Sp),
            Seq(Bar, Sp, D(38), Sp, Mapsto, Sp, N("v38"), Sp),
            Seq(Bar, Sp, D(39), Sp, Mapsto, Sp, N("v39"), Sp),
            Seq(Bar, Sp, D(40), Sp, Mapsto, Sp, N("v40"), Sp),
            Seq(Bar, Sp, D(41), Sp, Mapsto, Sp, N("v41"), Sp),
            Seq(Bar, Sp, D(42), Sp, Mapsto, Sp, N("v42"), Sp),
            Seq(Bar, Sp, D(43), Sp, Mapsto, Sp, N("v43"), Sp),
            Seq(Bar, Sp, D(44), Sp, Mapsto, Sp, N("v44"), Sp),
            Seq(Bar, Sp, D(45), Sp, Mapsto, Sp, N("v45"), Sp),
            Seq(Bar, Sp, D(46), Sp, Mapsto, Sp, N("v46"), Sp),
            Seq(Bar, Sp, D(47), Sp, Mapsto, Sp, N("v47"), Sp),
            Seq(Bar, Sp, D(48), Sp, Mapsto, Sp, N("v48"), Sp),
            Seq(Bar, Sp, D(49), Sp, Mapsto, Sp, N("v49"), Sp),
            Seq(Bar, Sp, D(50), Sp, Mapsto, Sp, N("v50"), Sp),
            Seq(Bar, Sp, D(51), Sp, Mapsto, Sp, N("v51"), Sp),
            Seq(Bar, Sp, D(52), Sp, Mapsto, Sp, N("v52"), Sp),
            Seq(Bar, Sp, D(53), Sp, Mapsto, Sp, N("v53"), Sp),
            Seq(Bar, Sp, D(54), Sp, Mapsto, Sp, N("v54"), Sp),
            Seq(Bar, Sp, D(55), Sp, Mapsto, Sp, N("v55"), Sp),
            Seq(Bar, Sp, D(56), Sp, Mapsto, Sp, N("v56"), Sp),
            Seq(Bar, Sp, D(57), Sp, Mapsto, Sp, N("v57"), Sp),
            Seq(Bar, Sp, Underscore, Sp, Mapsto, Sp, N("v58"))));


    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    private static Formula X(string name) => F.Id(name);

    private static Formula N(string name) => Q(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { NamePart(s) } : new[] { Dot, NamePart(s) }).ToArray());
    private static Formula NamePart(string name)
    {
        bool prime = name.EndsWith('\'');
        var words = name.Replace("'", "").Split('_');
        Formula result = F.Id(words[^1]);
        for (int i = words.Length - 2; i >= 0; --i)
            result = Seq(F.Id(words[i]), Underscore, Grp(result));
        return prime ? Seq(Operatorname, Grp(result), Apos) : Seq(Operatorname, Grp(result));
    }

    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula If(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Nat() => N("Nat");
    private static Formula IntType() => N("Int");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula OmegaProof() => Seq(N("by"), Sp, N("omega"));
    private static Formula FinMk(Formula x, Formula proof) => Call("Fin.mk", x, proof);
    private static Formula Vector() => Arrow(Fin(D(8192)), IntType());
    private static Formula ZeroVector() => Call("Function.const", Fin(D(8192)), D(0));
    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool literature = false,
        bool acknowledgeSource = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) :
                acknowledgeSource ? AssessedProvenance.FromRepo(Source) :
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

}
