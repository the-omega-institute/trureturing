using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class C129QubitBargmannDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered qubit Bargmann trace is the Bloch scalar-plus-oriented-volume formula.",
        H("C129 qubit three-label orientation"), Blocks(
            Describe.Lean(DescribeId.Create("c129-qubit-bargmann-triple-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch"),
                H("Bloch formula for the ordered qubit trace"),
                StatementSource.FromAuthor(Disp(TripleFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity is proved by expanding the three explicit two by two matrices. It is stated for arbitrary real three-coordinate vectors; unit-norm vectors give the pure-qubit interpretation from the source atom. The scalar terms are the three pairwise dot products and the imaginary term is the oriented scalar triple product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("c129-qubit-bargmann-explicit-bloch"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation"),
                H("Opposite Bloch orientations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered coordinate triples (0,0,1), (1,0,0), and (0,±1,0) give the two values (1+i)/4 and (1-i)/4. The pairwise dot products vanish while the oriented triple product changes sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("c129-qubit-bargmann-explicit-states"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation"),
                H("Explicit pure-state witnesses"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For v₁=|0⟩, v₂=(|0⟩+|1⟩)/√2, and v₃±=(|0⟩±i|1⟩)/√2, the rank-one density matrices have ordered traces (1±i)/4. This records the concrete two-sign witness; the remaining geometric interpretation of zero added orthogonal remainder stays in the source prose."))),
                DescribeRole.Theorem))));

    private static Formula TripleFormula()
    {
        Formula r1 = X("r_1"), r2 = X("r_2"), r3 = X("r_3");
        Formula real = Reals();
        Formula vector = Arrow(FinOf(D(3)), real);
        Formula dot12 = At(Qualified("dotProduct"), r1, r2);
        Formula dot23 = At(Qualified("dotProduct"), r2, r3);
        Formula dot31 = At(Qualified("dotProduct"), r3, r1);
        Formula triple = At(Qualified("dotProduct"), r1,
            At(Qualified("crossProduct"), r2, r3));
        Formula scalar = Add(Add(Add(Typed(D(1), real), dot12), dot23), dot31);
        Formula complexScalar = RealToComplex(scalar);
        Formula imaginary = Multiply(Multiply(RealToComplex(triple), UnitI()), UnitI());
        Formula rhs = Add(new Formula.Fraction(complexScalar, D(4)),
            new Formula.Fraction(Multiply(RealToComplex(triple), UnitI()), D(4)));
        return All("r_1", vector, All("r_2", vector, All("r_3", vector,
            Equal(Call("tripleBargmann", r1, r2, r3), rhs))));
    }

    private static Formula UnitI() => Seq(Mathrm, Grp(F.Id("i")));
    private static Formula RealToComplex(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula value) => At(Qualified("Fin"), value);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula X(string name) => F.Id(name);
}
