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
  var raw = @[byte]( int2byte 0xfa
                   , int2byte 0x01
                   , int2byte 0x01
                   , int2byte 0x00
                   , int2byte 0x05
                   , int2byte 0x01 //
                   , int2byte 0x1b
                   , int2byte 0x00
                   , int2byte 0x02
                   , int2byte 0x01
                   , int2byte 0x54 // 1
                   , int2byte 0x01, int2byte 0xff
                   , int2byte 0x00, int2byte 0x1b
                   , int2byte 0x54 // 2
                   , int2byte 0x00, int2byte 0xe2
                   , int2byte 0x40, int2byte 0x1f
                   , int2byte 0x54 // 3
                   , int2byte 0x26, int2byte 0xde
                   , int2byte 0x0a, int2byte 0x5e
                   , int2byte 0x54 // 4
                   , int2byte 0x02, int2byte 0x03
                   , int2byte 0x00, int2byte 0x00
                   , int2byte 0xce
                   , int2byte 0xaa, int2byte 0xb2
                   )
  val () = s := $BS.pack( view@raw| addr@raw, i2sz 33, i2sz 33)
  val packages = $Vicpack.parse s
  implement list_vt_foreach$fwork<$Vicpack.Vicpack><void>( x, env) = {
    val () = $Vicpack.print_vicpack( x)
  }
  val env = ()
  val () = list_vt_foreach<$Vicpack.Vicpack>( packages )
  val () = assertloc( list_vt_length packages = 1) // driver info and 0x54
  implement list_vt_freelin$clear<$Vicpack.Vicpack>( x) = {
    val () = $Vicpack.free x
  }
  val () = list_vt_freelin( packages)
  val () = $BS.free( view@raw | s)
}