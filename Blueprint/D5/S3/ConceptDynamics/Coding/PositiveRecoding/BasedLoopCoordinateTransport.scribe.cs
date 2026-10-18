using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class BasedLoopCoordinateTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed RS loops change coefficient basis through two triangles before endpoint cancellation.",
        H("Closed RS loops change coefficient basis through two triangles before endpoint cancellation"),
        Blocks(
            Paragraph(Text("The reusable operation is transport of a closed loop through a complete two-triangle square. Subtracting equal endpoint terms is justified only after the same actual time map occurs at both ends. Rectangular change matrices and zero-dimensional bases remain admissible.")),
            Describe.Lean(
                DescribeId.Create("basedloopcoordinatetransport-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/BasedLoopCoordinateTransport.factor_coordinates"),
                H("Both factors change coordinates on the right"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let V be an arbitrary module over GyrationDyadic in universe u, with bases b indexed by Fin n and c indexed by Fin m. changeRows b c is rows b c of LinearMap.id, of size n by m. An old row of coefficients multiplied on the right by C becomes the new row. rows(b,b,f)*C = C*rows(c,c,f) follows from rows_comp. changeRows_inverse proves C*Cinv=1, and its reversed application proves Cinv*C=1, including zero ranks. The path client uses the factor equation separately for its actual forward and backward maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("basedloopcoordinatetransport-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/BasedLoopCoordinateTransport.closed_square"),
                H("Two triangles retain the equal endpoint terms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any nonzero d divisible by three, bases b,c, and endomorphisms r,s,T with s.comp r=T and r.comp s=T, closed_square gives value(b,b,r,s)+value(b,c,id,T)=value(b,c,id,T)+value(c,c,r,s). Apply value_triangle first to b,b,c with r,id,s, and then to b,c,c with id,r,s. Only the literal RS equations identify the two boundary contributions. T may be singular; neither boundary is assumed zero. This theorem does not assert basis invariance of an individual open edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("basedloopcoordinatetransport-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/BasedLoopCoordinateTransport.path_rebased"),
                H("Recover the same loop unit in an arbitrary endpoint basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given w : FiniteKernelLadder.Path X X k and IsUnit X.time, for any c indexed by Fin m the finite kernel ladder returns a genuine endomorphism unit a whose value is w.forward. The recovered map commutes with T=X.time. Set s=T*a inverse in COLUMN order; both s.comp a=T and a.comp s=T are proved. The two coordinate intertwining equations are supplied for a and s, and for every nonzero d divisible by three the boundary equation precedes the canceled equality w.weight d=dyadicGyration d rowUnit(c,a) (rowUnit(c,a) inverse * rows(c,c,T)). The ROW backward factor has this order because rows transposes toMatrix. Only X.time must be a unit; no intermediate rank or time invertibility is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("basedloopcoordinatetransport-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/BasedLoopCoordinateTransport.inverse_time_order"),
                H("The native backward factor uses proved commutation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any unit a of the endomorphism ring and endomorphism T, Commute a T implies T*a inverse=a inverse*T. This consumed algebraic helper uses both unit inverse laws. The preserved original application applies it after recovering the actual loop unit, to compare the COLUMN factor T*U inverse with the original arithmetic convention U inverse*T. It is an application of standard unit commutation, with no independent novelty claim."))),
                DescribeRole.Theorem))));
}
