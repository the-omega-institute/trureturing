using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.CycleUniformMixing;
internal sealed class OrbitIncidenceCheckerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tree evaluation and finite Fourier identities support the exclusion of uniform mixing on the cycle with twenty-one vertices.",
        H("OrbitIncidenceChecker"), Blocks(
            Node("c21-orbitincidencechecker-checked-inc", "checked_inc", Disp(Seq(Forall, Sp, Parenthesized(Seq(Call("K"), Sp, Colon, Sp, Call("Type"))), Sp, Seq(OpenBracket, Seq(Call("CommRing"), Sp, Call("K")), CloseBracket), Sp, Parenthesized(Seq(Call("F"), Sp, Colon, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp"), Sp, To, Sp, Call("K"))), Sp, Parenthesized(Seq(Call("src"), Sp, Colon, Sp, Call("Nat"), Sp, To, Sp, Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp"), Sp, Times, Sp, Call("Int"))))), Sp, Parenthesized(Seq(Call("rep"), Sp, Colon, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp"))), Sp, Parenthesized(Seq(Call("t"), Sp, Colon, Sp, Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree"), Sp, Call("Nat"))))), Sp, Comma, Sp, Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.checkInc"), Sp, Call("src"), Sp, Call("rep"), Sp, Call("t"), Sp, Eq, Sp, Call("true"))), Sp, To, Sp, Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalInc"), Sp, Call("F"), Sp, Call("src"), Sp, Call("t"), Sp, Eq, Sp, Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.coefficientSum"), Sp, Call("src"), Sp, Call("t"), Sp, Colon, Sp, Call("K"))), Sp, Cdot, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm"), Sp, Call("F"), Sp, Call("rep"))))), "Every accepted incidence tree evaluates to its total coefficient times the orbit sum of its representative. Node composition preserves this equality.", "D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.checked_inc", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("c21-orbitincidencechecker-data-certificatescalar", "certificateScalar", Disp(Seq(Call("certificateScalar"), Sp, Colon, Sp, Call("Nat"))), "The fixed natural scalar in the integer Laurent certificate has the displayed type. Its value is specified by the Lean definition.", "D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.certificateScalar", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("c21-orbitincidencechecker-data-identity", "identity", Disp(Seq(Forall, Sp, Parenthesized(Seq(Call("K"), Sp, Colon, Sp, Call("Type"))), Sp, Seq(OpenBracket, Seq(Call("CommRing"), Sp, Call("K")), CloseBracket), Sp, Parenthesized(Seq(Call("F"), Sp, Colon, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp"), Sp, To, Sp, Call("K"))), Sp, Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("List.range"), Sp, D(1,4,9,7,3,6))), Sp, Dot, Sp, Call("map"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("i"), Sp, Mapsto, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source"), Sp, Call("i"))), Sp, Dot, Sp, D(2), Sp, Colon, Sp, Call("K"))), Sp, Cdot, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm"), Sp, Call("F"), Sp, Parenthesized(Seq(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source"), Sp, Call("i"))), Sp, Dot, Sp, D(1))))), Sp, Dot, Sp, Call("sum"), Sp, Eq, Sp, Parenthesized(Seq(Call("certificateScalar"), Sp, Colon, Sp, Call("K"))), Sp, Cdot, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm"), Sp, Call("F"), Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.zeroExp"))), "The displayed identity is used in the orbit-sum and spectral calculation.", "D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.identity", DescribeRole.Theorem, AssessedProvenance.FromRepo())), []));
    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Prose(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Inline[] Prose(string value)
    {
        var pieces = value.Split('$');
        var items = new System.Collections.Generic.List<Inline>();
        for (var i = 0; i < pieces.Length; i++)
            items.Add(i % 2 == 0 ? Text(pieces[i]) : Math(In(
                pieces[i] == "C_{n}" ? Seq(F.Id("C"), Underscore, Grp(F.Id("n"))) :
                Seq(F.Id("C"), Underscore, Grp(D(3)), Comma, Sp, F.Id("C"), Underscore, Grp(D(4))))));
        return items.ToArray();
    }
    private static Formula Call(string name) => name switch
    {
        "certificateScalar" => Seq(Operatorname, Grp(F.Id("certificateScalar"))),
        "CommRing" => Seq(Operatorname, Grp(Seq(F.Id("CommRing")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("Data"), Dot, F.Id("source")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("Exp")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("Index"), Dot, F.Id("Tree")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.checkInc" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("checkInc")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.coefficientSum" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("coefficientSum")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalInc" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("evalInc")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("norm")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.zeroExp" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("zeroExp")))),
        "F" => Seq(Operatorname, Grp(Seq(F.Id("F")))),
        "Int" => Seq(Operatorname, Grp(Seq(F.Id("Int")))),
        "K" => Seq(Operatorname, Grp(Seq(F.Id("K")))),
        "List.range" => Seq(Operatorname, Grp(Seq(F.Id("List"), Dot, F.Id("range")))),
        "Nat" => Seq(Operatorname, Grp(Seq(F.Id("Nat")))),
        "Type" => Seq(Operatorname, Grp(Seq(F.Id("Type")))),
        "fun" => Seq(Operatorname, Grp(Seq(F.Id("fun")))),
        "i" => Seq(Operatorname, Grp(Seq(F.Id("i")))),
        "map" => Seq(Operatorname, Grp(Seq(F.Id("map")))),
        "rep" => Seq(Operatorname, Grp(Seq(F.Id("rep")))),
        "src" => Seq(Operatorname, Grp(Seq(F.Id("src")))),
        "sum" => Seq(Operatorname, Grp(Seq(F.Id("sum")))),
        "t" => Seq(Operatorname, Grp(Seq(F.Id("t")))),
        "true" => Seq(Operatorname, Grp(Seq(F.Id("true")))),
        _ => throw new System.ArgumentException("Unknown Lean constant", nameof(name)),
    };

}
