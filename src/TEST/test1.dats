#include "share/atspre_staload.hats" // include template definitions

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"
staload "{$LIBS}/ats-bytestring/SATS/bytestring.sats"
staload Vicpack="./../SATS/vicpack.sats"

extern castfn
  int2byte
  {n: nat| n <= 255}
  ( i: int n
  ):<> byte

implement main0() = {
  var s: $BS.Bytestring0
  var raw = @[byte]( int2byte(0xfa)
                   , int2byte(0x01)
                   , int2byte(0x3c)
                   , int2byte(0x00)
                   , int2byte(0x03)
                   , int2byte(0x01) //
                   , int2byte(0x02)
                   , int2byte(0x00)
                   , int2byte(0x01)
                   , int2byte(0x01) 
                   , int2byte(0x14) //
                   , int2byte(0x00)
                   , int2byte(0x00)
                   , int2byte(0x64)
                   , int2byte(0x2c)
                   , int2byte(0x15) //
                   , int2byte(0x00)
                   , int2byte(0x00)
                   , int2byte(0x59)
                   , int2byte(0x06)
                   , int2byte(0xce) //
                   , int2byte(0xf9)
                   , int2byte(0x98))
  val () = s := $BS.pack( view@raw| addr@raw, i2sz 23, i2sz 23)
  val () =
    case+ $Vicpack.parse s of
    | ~list_vt_nil() => ()
    | packages => {
      implement list_vt_foreach$fwork<$Vicpack.Vicpack><void>( x, env) = {
        val () = $Vicpack.print_vicpack( x)
      }
      val env = ()
      val () = list_vt_foreach<$Vicpack.Vicpack>( packages )
      implement list_vt_freelin$clear<$Vicpack.Vicpack>( x) = {
        val () = $Vicpack.free x
      }
      val () = list_vt_freelin( packages)
    }
  val () = $BS.free( view@raw | s)
}