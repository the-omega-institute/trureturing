using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class ProbeComponentRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal density-input probability preservation forces scalar Kraus action on the complex span of each nonorthogonality component.",
        H("ProbeComponentRigidity"),
        Blocks(
            Describe.Lean(DescribeId.Create("kraus-inner"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_inner"),
                H("Kraus inner-product preservation"), StatementSource.FromAuthor(Disp(KrausInnerFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite Kraus family whose adjoint Gram sum is identity preserves every complex inner product after summing over the environment index."))), DescribeRole.Lemma),
            Paragraph(Text("Let unit complex vectors form an arbitrary index family in a finite dimensional Hilbert space. Nonzero overlap generates an equivalence relation. Each class determines the span of all probes in that class. Probability preservation is required for every density input, rather than only an individual input state. The dual map fixes every probe projection. Expanding the positive sum of squared Kraus commutators forces each commutator to vanish. The scalar actions agree across nonzero overlaps, extend along finite chains, and then extend linearly over the whole component. Mayer and Knill Theorem 1 gives the connected rigidity statement; Koashi and Imoto give broader nondisturbance structure.")),
            Describe.Lean(
                DescribeId.Create("kraus-normalized-of-channel"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_normalized_of_channel"),
                H("kraus normalized of channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/bluhmrauberwolf2018compression")),
                Blocks(Paragraph(Text("Trace preservation of a canonical rectangular channel implies adjoint-Gram normalization for every finite Kraus representation. The channel scalarity and canonical flagged-port factorization consume this supplier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-preserving-kraus-commute"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.probability_preserving_kraus_commute"),
                H("probability preserving kraus commute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("For every normalized finite Kraus representation preserving each probe probability on all density inputs, every Kraus matrix commutes with every probe projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kraus-scalar-on-component"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_scalar_on_component"),
                H("kraus scalar on component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("For every Kraus index, every probe index, and every vector in its component span, the Kraus action equals a scalar times that vector. The scalar is the unit probe expectation of that Kraus matrix. No finiteness assumption is imposed on the probe family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("channel-component-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.channel_component_scalar"),
                H("channel component scalar"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("Every canonical completely positive trace-preserving channel satisfying the probability equations has a rectangular finite Kraus representation whose normalization and scalar action on every component are proved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("connected-probability-preserving-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.connected_probability_preserving_identity"),
                H("connected probability preserving identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("If the unit probe family spans the full space and every pair belongs to the same component, its probability-preserving Kraus channel equals identity on every complex matrix. Every Kraus matrix is a scalar identity. A probe index and an ambient basis index explicitly provide the nonempty interfaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("component-stinespring-form"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeComponentRigidity.component_stinespring_form"),
                H("component stinespring form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary"), LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance")),
                Blocks(Paragraph(Text("For each component the finite environment coefficients have squared norm one. Every vector in the component maps to its original system coordinates multiplied by the same environment coefficients. The coordinates are the actual Kraus Stinespring coordinates."))),
                DescribeRole.Theorem))));
    private static Formula KrausInnerFormula()
    {
        static Formula V(string n) => F.Id(n);
        static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
        static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
        static Formula All(Formula.BoundVariable[] b, Formula p) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. b], p);
        static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
        static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
        static Formula Bracket(Formula x) => Seq(OpenBracket,x,CloseBracket);
        static Formula Sum(Formula a, Formula s, Formula x) => Seq(F.Sum,Underscore,Grp(a,Sp,Colon,Sp,s),Sp,x);
        Formula d=V("d"), s=V("s"), k=V("K"), x=V("x"), y=V("y"), a=V("a");
        Formula complex=Seq(Mathbb,Grp(V("C")));
        Formula mat=Call("Matrix",d,d,complex);
        Formula vec=new Formula.TypeArrow(d,complex);
        Formula ka=App(k,a);
        Formula gram=new Formula.Binary(Call("conjTranspose",ka),FormulaBinaryOperator.Multiply,ka);
        Formula tp=Eq(Sum(a,s,gram),Num(1));
        Formula lhs=Sum(a,s,Call("dotProduct",Call("star",Call("mulVec",ka,x)),Call("mulVec",ka,y)));
        Formula body=new Formula.Logic(tp,FormulaLogicOperator.Implies,Eq(lhs,Call("dotProduct",Call("star",x),y)));
        return All([B("d",V("Type")),B("s",V("Type"))],Seq(
            Bracket(Call("Fintype",d)),Sp,Bracket(Call("DecidableEq",d)),Sp,Bracket(Call("Fintype",s)),Sp,
            All([B("K",new Formula.TypeArrow(s,mat)),B("x",vec),B("y",vec)],body)));
    }

}
