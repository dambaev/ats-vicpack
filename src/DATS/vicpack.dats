#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
staload "./../SATS/vicpack.sats"

#define LIBS_targetloc "../libs" (* search path for external libs *)
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload UN="prelude/SATS/unsafe.sats"

%{^
#include "arpa/inet.h"
%}

implement free_vicpack( i) =
  case+ i of
  | ~driver_info_vt() => ()
  | ~internal_battery_on_die_vt(_) => ()
  | ~internal_battery_vt(_) => ()
//  | ~internal_temperature_vt(_) => ()
//  | ~charge_vt(_) => ()
  | ~temperature_vt(_) => ()
  | ~humidity_vt(_) => ()
//  | ~presure_vt(_) => ()
//  | ~acceleration_x_vt(_) => ()
//  | ~acceleration_y_vt(_) => ()
//  | ~acceleration_z_vt(_) => ()
//  | ~switch_interrupt_vt(_) => ()
//  | ~audio_average_vt(_) => ()
//  | ~audio_max_vt(_) => ()
//  | ~audio_spl_vt(_) => ()
//  | ~ambient_light_visible_vt(_) => ()
//  | ~ambient_light_ir_vt(_) => ()
//  | ~ambient_light_uv_vt(_) => ()
  | ~co2_level_vt(_) => ()
//  | ~distance_vt(_) => ()
//  | ~sample_rate_vt(_) => ()
  | ~voc_iaq_vt(_) => ()
  | ~voc_temperature_vt(_) => ()
  | ~voc_humidity_vt(_) => ()
  | ~voc_pressure_vt(_) => ()
  | ~voc_ambient_light_vt(_) => ()
  | ~voc_sound_peak_vt(_) => ()
//  | ~tof_distance_vt(_) => ()
//  | ~accelerometer_status_vt(_) => ()
//  | ~voltage_vt(_) => ()
//  | ~voltage_dff_vt(_) => ()
//  | ~voltage_ref_vt(_) => ()
//  | ~falling_counter_vt(_) => ()
//  | ~rising_counter_vt(_) => ()
//  | ~gps_data_vt(_) => ()
//  | ~eco2_and_pir_vt(_) => ()
  | ~evoc_eco2_vt(_) => ()
//  | ~device_id_vt(_) => ()
//  | ~device_pin_vt(_) => ()
//  | ~rssi_level_vt(_) => ()
//  | ~cell_id_vt(_) => ()

(* converts integer to byte *)
extern castfn
  i2c
  {n: nat | n <= 255}
  ( i: int n
  ):<> char(n)
  
extern castfn
  c2i
  ( i: char
  ):<> int

implement parse( s) =
let
  prval () = $BS.lemma_bytestring_param(s)
  fun
    parse_packages
    {n,ln : nat | n <= 255}
    {ilen,ioffset,cap,ucap,refcnt:nat | ilen > 0; ilen == (ilen / 5) * 5}{dynamic:bool}{l:agz}
    .<n>.
    ( i: size_t n
    , acc0: list_vt( Vicpack, ln)
    , acc1: size_t
    , s: &($BS.Bytestring_vtype(ilen, ioffset, cap, ucap, refcnt, dynamic, l)) >> $BS.Bytestring_vtype( olen, ooffset, cap, ucap, refcnt, dynamic, l)
    ):
    #[olen,ooffset,oln: nat]
    ( list_vt( Vicpack, oln), size_t) =
    ifcase
    | i = i2sz 0 => (acc0, acc1)
    | length s < i2sz 5 => (acc0, acc1)
    | _ =>
    let
    in
      case+ parse_package s of
      | ~None_vt() =>
        if length s >= 5
        then parse_packages( i - i2sz 1, acc0, acc1 + i2sz 1, s)
        else (acc0, acc1 + 1)
      | ~Some_vt( package) =>
      if length s >= 5
      then parse_packages( i - i2sz 1, list_vt_cons( package, acc0), acc1, s)
      else (list_vt_cons( package, acc0), acc1)
    end
  val s_sz = length s
  var i: $BS.Bytestring0?
  val () = i := $BS.ref_bs_parent s
  val () = i := $BS.dropC( i2sz 5, i) // without header
  val packages_count_i = g1ofg0( $UN.cast{int} ( s[4]))
in
  if packages_count_i < 0
  then (list_vt_nil(), i2sz 0) where {
    val () = $BS.free( i, s)
  }
  else
  let
    val packages_count = i2sz packages_count_i
  in
    ifcase
    | s_sz < 13 => (list_vt_nil(), i2sz 0) where { (* at least 1 package with payload *)
      val () = $BS.free( i, s)
    }
    | s[0] != i2c 0xFA => (list_vt_nil(), i2sz 0) where {
      val () = $BS.free( i, s)
    }
    | s[s_sz - 3] != i2c 0xCE => (list_vt_nil(), i2sz 0) where {
      val () = $BS.free( i, s)
    }
    | packages_count < 1 => (list_vt_nil(), i2sz 0) where {
      val () = $BS.free( i, s)
    }
    | packages_count > 255 => (list_vt_nil(), i2sz 0) where {
      val () = $BS.free( i, s)
    }
    | length i < packages_count * (i2sz 5) => (list_vt_nil(), i2sz 0) where {
      val () = $BS.free( i, s)
    }
    | _ => res where {
      val () = i := $BS.takeC( packages_count * i2sz 5, i)
      val res = parse_packages( packages_count, list_vt_nil(), i2sz 0, i)
      val () = $BS.free( i, s)
    }
  end
end

fn
  c2bool (i: char):<> bool =
case+ c2i i of
| 0 => false
| _ => true

extern fn
  ntohs
  (i: uint16
  ):<> uint16 = "mac#"
extern fn
  ntohl
  (i: uint32
  ):<> uint32 = "mac#"

extern prfun
  bytes_takeout
  {a:t0ype}{n: nat}{l:addr}
  ( i: !array_v(char, l, n) >> ( array_v(char, l, n), a @ l)
  ):<>
  a @ l

extern prfun
  bytes_addback
  {a:t0ype}{n: nat}{l:addr}
  ( i: !( array_v(char, l, n), a @ l) >> (array_v(char, l, n))
  , i1: a @ l
  ):<> void

extern castfn
  int2double( i: int):<> double

extern castfn
  u162double( i: uint16):<> double

extern castfn
  u322double( i: uint32):<> double

extern castfn
  u322uint( i: uint32):<> uint

extern castfn
  uint162int
  ( i: uint16
  ):<> int

extern castfn
  uint162uc
  ( i: uint16
  ):<> uchar

extern castfn
  i2u16
  {n: nat}
  ( i: int n):<> uint16

extern castfn
  i2u32
  {n: nat}
  ( i: int n):<> uint32

extern castfn
  uint162uint
  ( i: uint16
  ):<> uint

extern castfn
  u322u16
  ( i: uint32
  ):<> uint16
  

(*
  this function swaps bytes in terms of http://docs.vicotee.com/manuals/decodingpayload/QuickGuideVicPack in a uint32 value into 2 uint16 values
*)
fn
  swap_words( i: uint32):<> (uint16, uint16) = ($UN.cast{uint16}first, $UN.cast{uint16}second) where {
  infixr (+) .|.
  overload .|. with g0uint_lor_uint32
  infixr ( * ) .&.
  overload .&. with g0uint_land_uint32
  infixr (+) >>
  overload >> with g0uint_lsr_uint32
  infixr (+) <<
  overload << with g0uint_lsl_uint32
  val first = ((((i   .&.   ($UN.cast{uint32}0x00ff0000)) >> 16) .&. ($UN.cast{uint32}0xff)) << 8)
            .|. ((i  .&.  ($UN.cast{uint32}0xff000000)) >> 24)  .&. ($UN.cast{uint32}0xff)
  val second = (((i  .&.  ($UN.cast{uint32}0x000000ff)))        .&. ($UN.cast{uint32}0xff) << 8)
             .|. ((i .&. ($UN.cast{uint32}0x0000ff00)) >> 8)    .&. ($UN.cast{uint32}0xff)
}

implement parse_package{len,offset,cap,ucap,refcnt}( s) =
let
  prval () = $BS.lemma_bytestring_param( s)
  val package_type = c2i( s[0])
in
  case+ package_type of
  | 0x01 => Some_vt( driver_info_vt()) where {
    val () = s := $BS.dropC( i2sz 5, s)
  }
//  | 0x01 => Some_vt( driver_info_vt( @{ is_enabled=c2bool( s[1]), index=s[2], slot=s[3], type=s[4]}))
  | 0x07 => Some_vt( internal_battery_on_die_vt( result )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val result = ntohl netdata
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x08 => Some_vt( internal_battery_vt result) where {
    var data: $BS.Bytestring0?
    var meas = @[double]( 3.32211667225159
                        , 2.80515334784856
                        , 2.40084388357319
                        , 2.29739470604636
                        , 1.8957659397271
                        , 1.59635358098812
                        )
    var real = @[double]( 3.46
                        , 3.1
                        , 2.71
                        , 2.99
                        , 2.8
                        , 2.66
                        )
    val meas_sz = i2sz 6
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val raw = ntohl netdata
(* manual defines this way of handling of this package, but the reference implementation just divides raw value on 1000000.0 and has the same code commented out
    val volt = u322double( raw) * (0.18 / (int2double(g0int_npow(2, 10)))) * 2.0
    val ofnd = loop( i2sz 0, meas, meas_sz) where {
      fun
        loop
        {n:nat}{m:nat | n + 1 <= m}
        .<m - n>.
        ( i: size_t n
        , arr: &(@[double][m])
        , sz: size_t m
        ):<>
        Option_vt( @([n1:nat | n1 + 1 < m] size_t(n1), double)) =
      if i + 1 = sz
      then None_vt()
      else
        if (volt >= arr[i]) && (volt <= arr[i + i2sz 1])
        then Some_vt( (i, norm)) where {
          val norm = (volt - arr[ i + i2sz 1]) / (arr[i] - arr[i + i2sz 1])
        }
        else loop( i + i2sz 1, arr, sz)
    }
    val result =
      case+ ofnd of
      | ~None_vt() => volt
      | ~Some_vt( @(i, norm)) => real[ i + i2sz 1] - real[ i + i2sz 1] * norm + real[i] * norm
*)
    val result = u322double( raw) / 1000000.0
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x14 => Some_vt( temperature_vt(result )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val raw = ntohl netdata
    val result = u322double( raw) * 175.72 / 65536.0 - 46.85
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x15 => Some_vt( humidity_vt(result )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val result = g0uint_sub_uint32( g0uint_div_uint32( g0uint_mul_uint32((ntohl netdata), i2u32(125)), i2u32(65536)), i2u32(6))
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x21 => Some_vt( co2_level_vt(result )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val result = ntohl netdata
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x2B => Some_vt( voc_iaq_vt( @{state = uint162uc state, index=index} )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata:uint32 = ntohl !ptr
    val raw_value = ntohs ( u322u16 netdata)
    val state = g0uint_land_uint16(g0uint_lsr_uint16( raw_value, 14), i2u16(3))
    val index = g0uint_land_uint16(raw_value, i2u16 0x3FFF)
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x2C => Some_vt( voc_temperature_vt( u162double(raw_value) / 10.0 )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata:uint32 = ntohl !ptr
    val raw_value = g0uint_land_uint16( ntohs (u322u16 netdata), i2u16 0xFFFF)
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  (* TODO: there is an error either in manual, which says / 10.0 and vicpack.js, which uses / 100.0 *)
  | 0x2D => Some_vt( voc_humidity_vt( u162double(raw_value) / 100.0 )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = ntohl !ptr
    val raw_value = g0uint_land_uint16( ntohs (u322u16 netdata), i2u16 0xFFFF)
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x2E => Some_vt( voc_pressure_vt( u162double(raw_value) * 10.0 )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val raw_value0 = ntohl !ptr
    val raw_value1 = ((raw_value0 >> 8) & $UN.cast{uint32} 255) .|. ((raw_value0 & $UN.cast{uint32} 255) << 8) where {
      overload >> with g0uint_lsr_uint32
      overload << with g0uint_lsl_uint32
      infixr (+) .|.
      overload .|. with g0uint_lor_uint32
      infixr ( * ) &
      overload & with g0uint_land_uint32
    }
    val raw_value = $UN.cast{uint16}(raw_value1) & $UN.cast{uint16}(0xffff) where {
      infixr ( * ) &
      overload & with g0uint_land_uint16
    }
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x2F =>
  let
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = ntohl !ptr
    val raw_value = ntohs (u322u16 netdata)
    val exp = g1ofg0( uint162int(g0uint_lsr_uint16( raw_value, 12)))
    val mantissa = g0uint_land_uint16( raw_value, $UN.cast{uint16}4095)
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  in
    if exp < 0
    then None_vt()
    else Some_vt( voc_ambient_light_vt( u162double(mantissa) * 0.01 * int2double( g0int_npow(2, exp)) ))
  end
  | 0x30 => Some_vt( voc_sound_peak_vt( g0uint_div_uint16( raw_value, i2u16 10) )) where {
    var data: $BS.Bytestring0?
    val () = data := $BS.ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = ntohl !ptr
    val raw_value = ntohs (u322u16 netdata)
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
    val () = s := $BS.dropC( i2sz 5, s)
  }
  | 0x54 =>
    let
      val s_sz = length s
    in
      if s_sz < 20
      then None_vt() where {
        val () = s := $BS.dropC( i2sz 5, s)
        prval () = prop_verify{len < 20}()
      }
      else
        ifcase
        | s[i2sz 5] != i2c 0x54 => None_vt() where {
          val () = s := $BS.dropC( i2sz 5, s)
          prval () = prop_verify{len >= 20}()
        }
        | s[10] != i2c 0x54 => None_vt() where {
          val () = s := $BS.dropC( i2sz 5, s)
        }
        | s[15] != i2c 0x54 => None_vt() where {
          val () = s := $BS.dropC( i2sz 5, s)
        }
        | _ => Some_vt( evoc_eco2_vt( evoc_eco2)) where {
          val (pf0 | p1_p, p1_sz) = $BS.bs2bytes( s)
(* we need this struct to have alignment of 1 byte in order to match data of the packages *)
%{^
#pragma pack( push, 1)
struct evoc_eco2_t {
  uint8_t  atslab__p0_f0;
  uint32_t atslab__p0_f1;
  uint8_t  atslab__p1_f0;
  uint32_t atslab__p1_f1;
  uint8_t  atslab__p2_f0;
  uint32_t atslab__p2_f1;
  uint8_t  atslab__p3_f0;
  uint32_t atslab__p3_f1;
};
#pragma pack( pop)
%}
          typedef evoc_eco2_t = $extype_struct"struct evoc_eco2_t" of 
            { p0_f0 = uint8
            , p0_f1 = uint32
            , p1_f0 = uint8
            , p1_f1 = uint32
            , p2_f0 = uint8
            , p2_f1 = uint32
            , p3_f0 = uint8
            , p3_f1 = uint32
            }
          prval pf = bytes_takeout{evoc_eco2_t}(pf0)
          val @{ p0_f0 = p0, p0_f1 = p0_f1
              , p1_f0 = p1, p1_f1 = p1_f1
              , p2_f0 = p2, p2_f1 = p2_f1
              , p3_f0 = p3, p3_f1 = p3_f1
              }:evoc_eco2_t = !p1_p // pattern patch the data in packages
          val (static_iaq, eco2) = swap_words( p0_f1)
          val (iqa_raw, voc_temperature_raw) = swap_words( p1_f1)
          val (voc_humidity_raw, voc_pressure_raw) = swap_words( p2_f1)
          val (ambient_light, noise_level_raw) = swap_words( p3_f1)
          prval () = bytes_addback( pf0, pf)

          val iqa = g0uint_land_uint16( iqa_raw, $UN.cast{uint16} 0x03ff)
          val iqa_state = g0uint_land_uint16( g0uint_lsr_uint16( iqa_raw, 14), $UN.cast{uint16} 0x03)
          val temperature = ($UN.cast{float}voc_temperature_raw) / 10.0f

          val humidity = ($UN.cast{float}( voc_humidity_raw)) / ($UN.cast{float}100.0)
          val pressure = ($UN.cast{float}(voc_pressure_raw)) / 10.0f

          val noise_level = ($UN.cast{float}noise_level_raw)/ 10.0f

          prval () = $BS.bytes_addback( pf0 | s)

          val evoc_eco2 = @{ Static_IAQ = static_iaq
                          , eCO2 = eco2
                          , IQA = iqa
                          , IQA_State = iqa_state
                          , voc_temperature = temperature
                          , voc_humidity = humidity
                          , voc_pressure = pressure
                          , ambient_light = ambient_light
                          , noise_level = noise_level
                          }
          val () = s := $BS.dropC( i2sz 20, s)
        }
    end
  | _ => None_vt() where {
    val () = s := $BS.dropC( i2sz 5, s)
  }
end

implement print_vicpack( i) =
  case+ i of
  | driver_info_vt() =>
    println!( "DRIVER_INFO")
(*
    println!( "DRIVER_INFO: is_enabled = ", s.is_enabled, ", index=", c2i s.index, ", slot=", c2i s.slot, ", type=", c2i s.type)
*)
  | internal_battery_on_die_vt(_) =>
    println!("internal_battery_on_die")
  | internal_battery_vt(_) =>
    println!("internal_battery")
(*  
  | internal_temperature_vt(_) =>
    println!("internal_temperature")
*)
(*  
  | charge_vt(_) =>
    println!("charge")
*)
  | temperature_vt( value) =>
    println!("temperature: ", value)
  | humidity_vt( value) =>
    println!("humidity: ", value)
(*  
  | presure_vt(_) =>
    println!("presure")
*)
(*  
  | acceleration_x_vt(_) =>
    println!("acceleration_x")
*)
(*  
  | acceleration_y_vt(_) =>
    println!("acceleration_y")
*)
(*  
  | acceleration_z_vt(_) =>
    println!("acceleration_z")
*)
(*  
  | switch_interrupt_vt(_) =>
    println!("switch_interrupt")
*)
(*  
  | audio_average_vt(_) =>
    println!("audio_average")
*)
(*  
  | audio_max_vt(_) =>
    println!("audio_max")
*)
(*  
  | audio_spl_vt(_) =>
    println!("audio_spl")
*)
(*  
  | ambient_light_visible_vt(_) =>
    println!("ambient_light_visible")
*)
(*  
  | ambient_light_ir_vt(_) =>
    println!("ambient_light_ir")
*)
(*  
  | ambient_light_uv_vt(_) =>
    println!("ambient_light_uv")
*)
  | co2_level_vt(_) =>
    println!("co2_level")
(*  
  | distance_vt(_) =>
    println!("distance")
*)
(*  
  | sample_rate_vt(_) =>
    println!("sample_rate")
*)
  | voc_iaq_vt(v) =>
    println!("voc_iaq= state=", $UN.cast{int}v.state, ", index=", v.index)
  | voc_temperature_vt(t) =>
    println!("voc_temperature=", t)
  | voc_humidity_vt(v) =>
    println!("voc_humidity=", v)
  | voc_pressure_vt(p) =>
    println!("voc_pressure=", p)
  | voc_ambient_light_vt(v) =>
    println!("voc_ambient_light=", v)
  | voc_sound_peak_vt(v) =>
    println!("voc_sound_peak=", v)
(*  
  | tof_distance_vt(_) =>
    println!("tof_distance")
*)
(*  
  | accelerometer_status_vt(_) =>
    println!("accelerometer_status")
*)
(*  
  | voltage_vt(_) =>
    println!("voltage")
*)
(*  
  | voltage_dff_vt(_) =>
    println!("voltage_dff")
*)
(*  
  | voltage_ref_vt(_) =>
    println!("voltage_ref")
*)
(*  
  | falling_counter_vt(_) =>
    println!("falling_counter")
*)
(*  
  | rising_counter_vt(_) =>
    println!("rising_counter")
*)
(*  
  | gps_data_vt(_) =>
    println!("gps_data")
*)
(*  
  | eco2_and_pir_vt(_) =>
    println!("eco2_and_pir")
*)
  | evoc_eco2_vt(v) =>
    println!( "evoc_eco2: Static_IAQ: ", v.Static_IAQ
            , ", eCO2: ", v.eCO2
            , ", IQA: ", v.IQA
            , ", IQA_State: ", v.IQA_State
            , ", voc_temperature: ", v.voc_temperature
            , ", voc_humidity: ", v.voc_humidity
            , ", voc_pressure: ", v.voc_pressure
            , ", ambient_light: ", v.ambient_light
            , ", noise_level: ", v.noise_level
            )
(*  
  | device_id_vt(_) =>
    println!("device_id")
*)
(*  
  | device_pin_vt(_) =>
    println!("device_pin")
*)
(*  
  | rssi_level_vt(_) =>
    println!("rssi_level")
*)
(*  
  | cell_id_vt(_) =>
    println!("cell_id")
*)

implement package2kvs( i) = 
let
  fn
    _list_vt_cons
    {n:nat}
    ( h: ($BS.BytestringNSH1, $BS.BytestringNSH1)
    , t: list_vt( ($BS.BytestringNSH1, $BS.BytestringNSH1), n)
    ):<>
    list_vt( ($BS.BytestringNSH1, $BS.BytestringNSH1), n + 1) = list_vt_cons( h, t)

  infixr (+) ::
  overload :: with _list_vt_cons
in
  case+ i of
  | driver_info_vt() =>
    list_vt_nil()
(*
  | driver_info_vt( s) =>
    ( $BS.pack "DRIVER_INFO.enabled", $BS.pack s.is_enabled)
    :: ( $BS.pack "DRIVER_INFO.index", $BS.pack s.index)
    :: ( $BS.pack "DRIVER_INFO.slot", $BS.pack s.slot)
    :: ( $BS.pack "DRIVER_INFO.type", $BS.pack s.type)
    :: list_vt_nil()
*)
  | internal_battery_on_die_vt(v) =>
    list_vt_cons( ( $BS.pack "internal_battery_on_die", $BS.pack v), list_vt_nil())
  | internal_battery_vt(v) =>
    list_vt_cons( ( $BS.pack "internal_battery", $BS.pack v), list_vt_nil())
(*  | internal_temperature_vt(v) =>
    ( $BS.pack "internal_temperature", $BS.pack v)
    :: list_vt_nil()
  | charge_vt(v) =>
    ( $BS.pack "charge", $BS.pack v)
    :: list_vt_nil()
*)
  | temperature_vt( v) =>
    list_vt_cons( ( $BS.pack "temperature", $BS.pack v), list_vt_nil())
  | humidity_vt( v) =>
    list_vt_cons( ( $BS.pack "humidity", $BS.pack v), list_vt_nil())
(*
  | presure_vt(v) =>
    ( $BS.pack "presure", $BS.pack v)
    :: list_vt_nil()
  | acceleration_x_vt(v) =>
    ( $BS.pack "acceleration_x", $BS.pack v)
    :: list_vt_nil()
  | acceleration_y_vt(v) =>
    ( $BS.pack "acceleration_y", $BS.pack v)
    :: list_vt_nil()
  | acceleration_z_vt(v) =>
    ( $BS.pack "acceleration_z", $BS.pack v)
    :: list_vt_nil()
  | switch_interrupt_vt(v) =>
    ( $BS.pack "switch_interrupt.button_pressed", $BS.pack v.button_pressed)
    ( $BS.pack "switch_interrupt.pin", $BS.pack v.pin)
    :: list_vt_nil()
  | audio_average_vt(v) =>
    ( $BS.pack "audio_average", $BS.pack v)
    :: list_vt_nil()
  | audio_max_vt(v) =>
    ( $BS.pack "audio_max", $BS.pack v)
    :: list_vt_nil()
  | audio_spl_vt(v) =>
    ( $BS.pack "audio_spl", $BS.pack v)
    :: list_vt_nil()
  | ambient_light_visible_vt(v) =>
    ( $BS.pack "ambient_light_visible", $BS.pack v)
    :: list_vt_nil()
  | ambient_light_ir_vt(v) =>
    ( $BS.pack "ambient_light_ir", $BS.pack v)
    :: list_vt_nil()
  | ambient_light_uv_vt(v) =>
    ( $BS.pack "ambient_light_uv", $BS.pack v)
    :: list_vt_nil()
*)
  | co2_level_vt(v) =>
    list_vt_cons( ( $BS.pack "co2_level", $BS.pack v), list_vt_nil())
(*
  | distance_vt(v) =>
    ( $BS.pack "distance", $BS.pack v)
    :: list_vt_nil()
  | sample_rate_vt(v) =>
    ( $BS.pack "sample_rate", $BS.pack v)
    :: list_vt_nil()
*)
  | voc_iaq_vt(v) =>
    list_vt_cons( ( $BS.pack "voc_iaq.state", $BS.pack ($UN.cast{uint32} v.state))
      , list_vt_cons( ( $BS.pack "voc_iaq.index", $BS.pack v.index)
        , list_vt_nil()
        )
      )
  | voc_temperature_vt(v) =>
    list_vt_cons( ( $BS.pack "voc_temperature", $BS.pack v), list_vt_nil())
  | voc_humidity_vt(v) =>
    list_vt_cons( ( $BS.pack "voc_humidity", $BS.pack v), list_vt_nil())
  | voc_pressure_vt(v) =>
    list_vt_cons( ( $BS.pack "voc_pressure", $BS.pack v), list_vt_nil())
  | voc_ambient_light_vt(v) =>
    list_vt_cons( ( $BS.pack "voc_ambient_light", $BS.pack v), list_vt_nil())
  | voc_sound_peak_vt(v) =>
    list_vt_cons( ( $BS.pack "voc_sound_peak", $BS.pack v), list_vt_nil())
(*  | tof_distance_vt(v) =>
    println!("tof_distance")
  | accelerometer_status_vt(v) =>
    println!("accelerometer_status")
  | voltage_vt(v) =>
    println!("voltage")
  | voltage_dff_vt(v) =>
    println!("voltage_dff")
  | voltage_ref_vt(v) =>
    println!("voltage_ref")
  | falling_counter_vt(v) =>
    println!("falling_counter")
  | rising_counter_vt(v) =>
    println!("rising_counter")
  | gps_data_vt(v) =>
    println!("gps_data")
  | eco2_and_pir_vt(v) =>
    println!("eco2_and_pir")
*)
  | evoc_eco2_vt(v) =>  
    ( $BS.pack "Static_IAQ", $BS.pack v.Static_IAQ)
    :: ($BS.pack "eCO2", $BS.pack v.eCO2)
    :: ($BS.pack "IQA", $BS.pack v.IQA)
    :: ($BS.pack "IQA_State", $BS.pack v.IQA_State)
    :: ($BS.pack "voc_temperature", $BS.pack v.voc_temperature)
    :: ($BS.pack "voc_humidity", $BS.pack v.voc_humidity)
    :: ($BS.pack "voc_pressure", $BS.pack v.voc_pressure)
    :: ($BS.pack "ambient_light", $BS.pack v.ambient_light)
    :: ($BS.pack "noise_level", $BS.pack v.noise_level)
    :: (list_vt_nil())
(*
  | device_id_vt(v) =>
    println!("device_id")
  | device_pin_vt(v) =>
    println!("device_pin")
  | rssi_level_vt(v) =>
    println!("rssi_level")
  | cell_id_vt(v) =>
    println!("cell_id")
*)
end
